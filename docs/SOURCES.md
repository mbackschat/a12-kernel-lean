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

The reusable provenance route is the measurement checkout's own `../a12-rulekit-measure/scripts/prepare-dmtool-source.sh` — a12-dmkits' script, not this repository's, and the prefix is load-bearing because `scripts/` here resolves to a directory that has never held it. It accepts only the checkout's exact clean HEAD, reuses or rebuilds the JVM launcher as needed, and verifies its reported revision before returning it. Each retained observation records the actual launcher and kernel versions from that run rather than inheriting the historical 2026-08-06 launcher identity. [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback) owns the probe method and the required persisted-read-back check.

**Two checkouts, and measurement runs in the second one.** `../a12-rulekit` stays the source of truth for reading peer code, findings, and specs, and remains strictly immutable. Observation commands run instead in the owner-approved read-only measurement checkout `../a12-rulekit-measure`, **pinned to a12-dmkits `2304a684939621a8848e1261be9ab8e6278dc532`**, re-pinned 2026-09-22 from `9c86459b352f7989b9dbdae80f71e6dd6cec6066` — deliberately, because `computeResults` and the inline-document fidelity fix land at `526778fa7`, which the previous pin predates, and the [applied-state measurement](sources/evaluation-and-application-routes.md#src-errored-target-applied-state) needs both.

The launcher was rebuilt at that pin and reports it clean through the same `prepare-dmtool-source.sh` route, `dmtool` 0.13.0, Kernel `30.8.1` built and runtime, catalog verified against 30.8.1; both checkouts read clean before and after. Receipts stamped an earlier pin stay valid as identities of their own bytes and are not comparable with a hash produced after a re-pin. The [2026-09-21 dispositions](#inbound-2026-09-21-corrections) own the previous re-pin.

The root [`CLAUDE.md`](../CLAUDE.md) carve-out owns the exception's limits, and nothing in it permits editing, staging, or extending either checkout. The reason is availability rather than capability: the primary checkout is normally dirty because a peer session is working it, and the preparation script refuses a dirty tree, which had reduced kernel correspondence to windows lasting under a minute.

The pin before the current one was taken 2026-09-08 from `6a669c56d`, for the reasons its [record](#inbound-2026-09-08-instrument) owns, and was verified there as `dmtool` 0.13.0, source clean, kernel `30.8.1` built and runtime.

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

Moved to [`archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md`](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md) when this hub neared its size ceiling. The anchors below keep every existing citation resolving.

<a id="reviewed-numeric-scale-continuity"></a>
- [Reviewed numeric-scale continuity](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-numeric-scale-continuity)
<a id="reviewed-pointer-and-operator-domain-batch"></a>
- [Reviewed pointer and operator-domain batch](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-pointer-and-operator-domain-batch)
<a id="src-2026-09-06-ladder-handback-detail"></a>
<a id="reviewed-group-count-multiplicity-batch"></a>
- [Reviewed group-count multiplicity batch](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-group-count-multiplicity-batch)
<a id="reviewed-group-operand-extent-and-coverage-batch"></a>
- [Reviewed group-operand extent and coverage batch](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-group-operand-extent-and-coverage-batch)
<a id="reviewed-compute-result-granularity-and-cascade-clear-kinds--the-axis-the-computation-rows-were-queuing-measurements-for"></a>
- [Reviewed compute result-granularity and cascade clear-kinds — the axis the computation rows were queuing measurements for](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-compute-result-granularity-and-cascade-clear-kinds--the-axis-the-computation-rows-were-queuing-measurements-for)
<a id="src-2026-09-07-extremum-and-orderability-handback"></a>
<a id="reviewed-2026-09-07-handback--the-extremum-leader-set-and-the-powers-derived-scale"></a>
- [Reviewed 2026-09-07 handback — the extremum leader set and the power's derived scale](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-2026-09-07-handback--the-extremum-leader-set-and-the-powers-derived-scale)
<a id="reviewed-per-carrier-group-operand-admission--the-extrema-row-this-project-had-queued-was-already-held"></a>
- [Reviewed per-carrier group-operand admission — the extrema row this project had queued was already held](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-per-carrier-group-operand-admission--the-extrema-row-this-project-had-queued-was-already-held)
<a id="reviewed-custom-field-type-leaf-observability-and-filtered-carrier-batch"></a>
- [Reviewed custom-field-type, leaf-observability, and filtered-carrier batch](archived/SOURCES-REVIEWED-BATCHES-THROUGH-2026-09-08.md#reviewed-custom-field-type-leaf-observability-and-filtered-carrier-batch)

### Inbound 2026-09-05 and 2026-09-06 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md`](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md) when this hub reached its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-05b"></a>
- [Reviewed 2026-09-05b handback — three entries accepted, one peer premise retracted, and one overlap found by reading](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-05b)
<a id="inbound-2026-09-05c"></a>
- [Reviewed 2026-09-05c handback — the reassigned row measured, and one over-admission found from a description of this project's code](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-05c)
<a id="inbound-2026-09-05d"></a>
- [Reviewed 2026-09-05d handback — the DateTime family's cross-kind comparison, the last item open between the two projects](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-05d)
<a id="inbound-2026-09-05e"></a>
- [Reported 2026-09-05e — `NumberOfDifferentValues`' temporal admission gate, with later local re-derivation](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-05e)
<a id="inbound-2026-09-05f"></a>
- [Reported 2026-09-05f — the distinct count's temporal identity is the decoded date, and the first-operand grid's envelope](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-05f)
<a id="inbound-2026-09-06b"></a>
- [Reported 2026-09-06b — the kernel supplies no diagnostic code at all, and every `MVK_*` this project consumes is a12-dmkits' extraction from the message](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-06b)
<a id="inbound-2026-09-06a"></a>
- [Reported 2026-09-06a — the operand/target binding relation transfers from the computation carrier to the rule carrier unchanged](archived/SOURCES-INBOUND-HANDBACKS-THROUGH-2026-09-06.md#inbound-2026-09-06a)

### Inbound 2026-09-26l handback

<a id="inbound-2026-09-26l-repeatable-root"></a>
#### Reviewed 2026-09-26l repeatable-root handback — a `RepetitionNotUnique` rule at a repeatable root holding every key compares the root's own rows across the document

a12-dmkits revision `70e16c71258092b66e50760dee742b092080f6d5` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26l`, frozen as sent in the user's exchange directory with SHA-256 `435f245eb4619abba545f80ff425e5c726544dab5807712798445a9e4756e7ef`. The lock was read at that revision, not run here. It answers no ledger entry and creates none. Its §2 reports the peer's own records, not recorded as a claim.

**Claim.** Its §1 (`RepetitionNotUniqueRepeatableRootDiffTest`, runtime, both Kernel strategies agreeing), each rule declared in the repeatable root `Fleet`. With `(Plate, Vin)` at `(A, 1)`, `(A, 1)`, `(B, 2)`, `RepetitionNotUnique(Plate, Vin)`, `RepetitionNotUnique(Plate)` and `RepetitionNotUnique(Plate @From /Fleet)`, reporting at `Plate`, fire `VALUE` at the first two vehicles; with `Vin` empty on those two the pair fires `OMISSION` and the sole key `VALUE`, scoped or not; with distinct plates none fires. `RepetitionNotUnique(Drivers/License)`, reporting at `License`, fires `VALUE` at both drivers of the vehicle listing `L-1` twice and not at the other vehicle's `L-1`.

**Lean.** Corrected. [`elaborateRepetitionNotUniqueSource`](../A12Kernel/Elaboration/RepetitionNotUnique.lean) had refused the root rule without a class; it now takes the root as the reference group, and [`RepetitionNotUniqueValidationRule`](../A12Kernel/Conformance/RepetitionNotUniqueValidationRule.lean) locks every row.

### Inbound 2026-09-26k handback

<a id="inbound-2026-09-26k-paired-gates"></a>
#### Reviewed 2026-09-26k paired-gate handback — `RepetitionNotUnique` reads every key and its scope before any gate, orders its key-list and placement gates pair by pair, and admits keys at a repeatable root

a12-dmkits revision `4c04bb1abd4b5e72b8bb2b4689b0bb578d57a076` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26k`, frozen as sent in the user's exchange directory with SHA-256 `d0f09b99cbd268f9b90dce27ffb2a046bf9346d233c388c0bb6bd452b3966ecc`. The locks were read at that revision, not run here. It answers no ledger entry and creates none. Its §7 and §9 report the peer's own records and its §8 asks which shape [SG9](gaps/paths-and-groups.md#gap-sg9)'s last unattributed source meant, answered in this project's receipt as its own §1 row reporting at `Reference`; none is recorded as a claim.

**Claim.** Its §1 to §5 (`RepetitionNotUniquePairedGateLawsTest`, the index-selected `Payments` scope row in `CheckerRepetitionNotUniquePairedGateAgreementTest` alone), on a root `Policy` holding a keyed repeatable `Claims`, a `Payments` keyed on the same field, an index-free `Batches` holding `Items` and `Parts` keyed on one `LineRef`, an index-free `Riders`, an empty repeatable `Vacant` and an empty fixed `Dormant`, beside a repeatable root `Fleet`; unless placed otherwise each rule is in `/Policy` reporting at `Claims/ClaimRef`.

A key that cannot be read answers ahead of each key-list gate in either position, and reporting at the root's `Reference`, `Reference, Claims/ClaimRef` draws `MVK_NO_WILDCARD`, and so it does with a category, a group, a star, a semantic-index key, the raw `Memo` or `Insured, Insured` added before or after `Claims/ClaimRef`. The scope is read with the keys: `@From Vacant` draws `MVK_NO_WILDCARD` over a sole raw key and over a duplicate pair, `@From Dormant` `MVK_GROUP_IS_EMPTY`, and reporting at `Reference` a keyed, an index-free and the empty scope draw `MVK_NO_WILDCARD`.

Each adjacent pair of the category, group, star, semantic-index and raw gates answers with the earlier gate's class in both orders, as does the group gate beside the raw one. `Insured, Insured` draws `MVK_DUPLICATE_PARAM1`, and `Insured, Insured/InsuredName` and `/Policy` beside `Claims/ClaimRef` in both orders `MVK_DUPLICATE_PARAM2`.

From a rule in `Claims`, `ClaimRef` beside `/Policy/Payments/PayRef` draws `MVK_NOT_IN_SAME_PATH` in both orders. Keys in the sibling fixed `Claims/Adjuster` and `Claims/Assessor` are admitted with and without `@From Claims`, while `Batches/Items/ItemRef, Batches/Parts/PartRef` draws `MVK_NOT_IN_SAME_PATH` and with `@From Batches` `MVK_PARALLEL_ITERATION_NOT_ALLOWED`. At `/Fleet`, `Plate` and `Plate, Vin` are admitted, `Registration/RegNo` alone and beside `Plate` draw `MVK_REPEATABLE_GROUP_MISSING`, and `Drivers/License` is admitted.

`@From Insured For "k"` draws `MVK_NO_INDEX_FIELD`, `@From Claims For ""` `MVK_INDEX_VALUE_INVALID`, `@From Claims For "C-1"`, beside `Claims/ClaimRef` or `Payments/PayRef`, `MVK_SEMANTIC_INDEX_NOT_ALLOWED`, `@From Claims*` `MVK_NO_WILDCARDS_ALLOWED`, `@From Vacant*` `MVK_GROUP_IS_EMPTY`, `@From Insured*` `MVK_INVALID_WILDCARD` and `@From Claims* For "C-1"` `MVK_SEMANTIC_INDEX_AND_WILDCARD`. From a rule in `Claims` reporting at `Reference`, `ClaimRef` and `/Policy/Reference @From /Policy/Claims` draw `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`.

**Lean.** Corrected. [`elaborateRepetitionNotUniqueSource`](../A12Kernel/Elaboration/RepetitionNotUnique.lean) read the scope after the key list's gates and asked an empty scope before its walk; it now reads the scope with the keys, walk first, and projects `MVK_PARALLEL_ITERATION_NOT_ALLOWED` for keys in parallel repeatable groups under a scope. [`RepetitionNotUniqueDiagnostic`](../A12Kernel/Conformance/RepetitionNotUniqueDiagnostic.lean) locks every row a plain field path can spell, the index-free `Notes` standing for `Riders`. Keys in sibling fixed groups reach this theory's topology limit, and an empty fixed group and a category, starred, index-selected or `$` key or scope have no spelling, which [SG9](gaps/paths-and-groups.md#gap-sg9) records.

<a id="inbound-2026-09-26k-empty-star"></a>
#### Reviewed 2026-09-26k empty-star handback — an empty group's missing star answers ahead of its emptiness on every group carrier, and an empty repeatable root starred draws the root class

It shares the provenance of the paired-gate record above and takes the letter's §6.

**Claim.** Its §6 (`CheckerRepetitionNotUniquePairedGateAgreementTest.aGroupsStarClassAnswersAheadOfItsEmptinessOnEveryCarrier`), each rule in `/Policy` reporting at `Reference` behind `FieldFilled(Reference)`. `GroupFilled(/Policy/Vacant)` and `NumberOfFilledGroups`, `AtLeastOneGroupFilled` and `NumberOfFilledFields` over `/Policy/Vacant, /Policy/Insured` draw `MVK_NO_WILDCARD`, `NumberOfFilledGroups(/Policy/Vacant*) > 0` `MVK_GROUP_IS_EMPTY` and `NumberOfFilledGroups(/Policy/Dormant*) > 0` `MVK_INVALID_WILDCARD`. On the empty repeatable root `Archive`, `GroupFilled(/Archive)` draws `MVK_NO_WILDCARD` and `NumberOfFilledGroups(/Archive*) > 0` `MVK_ROOT_GROUP_IS_EMPTY`, and on the empty fixed root `Attic`, `GroupFilled(/Attic*)` draws `MVK_INVALID_WILDCARD`.

**Lean.** Corrected once. The unstarred rows already drew the missing star on every carrier Lean holds for them; `NumberOfFilledFields` over two groups has none. A starred empty root had claimed no class; [`StarredGroupElabError.emptyGroupDiagnostic?`](../A12Kernel/Elaboration/StarGroup.lean) now projects `MVK_ROOT_GROUP_IS_EMPTY`, measured on the count and carried to the other carriers sharing that read as an assumption [SG9](gaps/paths-and-groups.md#gap-sg9) records, locked in [`GroupListDiagnostic`](../A12Kernel/Conformance/GroupListDiagnostic.lean). An empty fixed group has no representation.

### Inbound 2026-09-26j handback

<a id="inbound-2026-09-26j-count-star"></a>
#### Reviewed 2026-09-26j count-star handback — a lone unstarred repeatable group draws the missing star ahead of the count's arity, and a rule declared in the group binds it

a12-dmkits revision `7129827809d14f28af455eb3235cd471d537d735` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26j`, frozen as sent in the user's exchange directory with SHA-256 `5bfa9b7d952589d88d413b98aa9fd625c2ff1185bd798c009f5f6180b63f85fc`. The lock was read at that revision, not run here. It answers no ledger entry and creates none. Its §3 corrects the peer's own `-26d`, whose account `spec/05` already carries, its §4 reports the peer's own records, and its note that `KF242` agrees with `spec/07`'s filter scope-gate paragraph changes nothing here; none is recorded as a claim.

**Claim.** Its §1 and §2 (`GroupCountScopeOperandLawsTest`), on a root `Item` holding a fixed `Grading` and a repeatable `Keyed` indexed by its `Key`, beside a repeatable root `Lot`. At `/Item` reporting at `Title` behind `FieldFilled(Title)`, `NumberOfFilledGroups(…) > 0` over `Keyed`, `Grading, Keyed` and `/Lot` draws `MVK_NO_WILDCARD`, over `/Item` and `Grading` `MVK_PARAMSIZE_INVALIDGN`, and over `Keyed*` is admitted. In `/Item/Keyed` reporting at `Amount` behind `FieldFilled(/Item/Keyed/Amount)`, the count over `/Item/Grading, /Item/Keyed` and over `/Item/Keyed*` is admitted and over `/Item/Keyed` alone draws `MVK_PARAMSIZE_INVALIDGN`.

**Lean.** Corrected. The fixed-list count refused a lone group counted from inside it without a class; from the measured placement, a rule declared in the group with its error field there, it now meets the count's arity, every other placement still claiming no class, and [`GroupListDiagnostic`](../A12Kernel/Conformance/GroupListDiagnostic.lean) locks the lone rows from both placements. The paired count from inside the group refuses without a class, since the comparison route sees no guard.

### Inbound 2026-09-26i handback

<a id="inbound-2026-09-26i-expansion-order"></a>
#### Reviewed 2026-09-26i expansion-order handback — a group operand is read depth-first in declaration order, its index field in place, and its first field sets the list's family

a12-dmkits revision `2c2640e731377818a06a59446f315e6cef410d6f` on `main`, confirmed an ancestor of that checkout's `main` when read on 2026-09-26. The letter is the peer's `-2026-09-26i`, frozen as sent in the user's exchange directory with SHA-256 `166fc249834fc5accc1acd36cec8508adba21f92b6970566056718a1484efa4f`. The lock was read at that revision, not run here. It answers no ledger entry and creates none. Its §5 reports the peer's own records, not recorded as a claim.

**Claim.** Its §1 to §3 (`EntityListGroupExpansionKindLawsTest`), each rule at `/Item` behind `FieldFilled(Title)`. `NumberOfDifferentValues` over `Specs, Weight` draws `MVK_STRING_ENUM_AND_NON_STRING_ENUM`, over `Rekeyed*, Title` `MVK_NUMBER_AND_NON_NUMBER` although `Rekeyed`'s String index field follows its Number, over `Layered, Weight`, whose subgroup of a String precedes its Number, the String class, and over `Annotated, Weight`, whose Number precedes its subgroup of a String, the Number class, against `Grading, Weight` admitted.

`Sum` over `Keyed*`, whose index field is a String, over `Nested`, holding a String only in a subgroup, and over `Specs` alone draws `MVK_NO_NUMBER`, and `NumberOfDifferentValues(Keyed*, Title)` the String class, against `Sum(NumNested, Weight)` and `Sum(Grading)` admitted. `MaxValue(Released, Keyed*)` draws `MVK_DATE_AND_NONDATE` and `MaxValue(Released, Monthly*)` over a `yyyy-MM` group `MVK_DATEFORMATS_NOT_COMPATIBLE`, against `MaxValue(Dated*, Released)` admitted. Its §4: `NumberOfDifferentValues(Title, Keyed For "k")` draws the String class, the valid key reading cleanly.

**Lean.** No behaviour change. A group's expansion is the model's field list filtered to its subtree, which [`FlatModel.fields`](../A12Kernel/Elaboration/Flat/Types.lean) now states is the depth-first declaration order, and every row but the index-selected one agrees in [`GroupExpansionOrder`](../A12Kernel/Conformance/GroupExpansionOrder.lean). An index-selected group has no spelling on these carriers.

### Inbound 2026-09-26f through 2026-09-26h handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26h-empty-scope"></a>
- [Reviewed 2026-09-26h empty-scope handback — an empty `@From` scope draws the empty-group class ahead of the scope's repeat gate](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md#inbound-2026-09-26h-empty-scope)
<a id="inbound-2026-09-26h-list-reads"></a>
- [Reviewed 2026-09-26h list-read handback — eight more list carriers read every operand before their duplicate gate, the plural overlap before its scalar slot's gate, and both root gates ask an index-selected root](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md#inbound-2026-09-26h-list-reads)
<a id="inbound-2026-09-26g-type-match"></a>
- [Reviewed 2026-09-26g type-match handback — `FirstFilledValue`'s type match compares neither a Boolean's stored values nor a Number's fraction digits](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md#inbound-2026-09-26g-type-match)
<a id="inbound-2026-09-26f-gate-order"></a>
- [Reviewed 2026-09-26f gate-order handback — `RepetitionNotUnique` judges its key list gate by gate over the whole list before exactly one branch, and an outsider whose read is clean meets the rule-group gate](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26f-THROUGH-2026-09-26h.md#inbound-2026-09-26f-gate-order)

### Inbound 2026-09-26d and 2026-09-26e handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26e-labelled-target"></a>
- [Reviewed 2026-09-26e labelled-target handback — a String copied into an Enumeration draws the comparison class at a labelled target and the calculation's class at an unlabelled one](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md#inbound-2026-09-26e-labelled-target)
<a id="inbound-2026-09-26d-constant-typing"></a>
- [Reviewed 2026-09-26d constant-typing handback — a written-out constant is typed by its shape and the calendar before the comparison walk](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md#inbound-2026-09-26d-constant-typing)
<a id="inbound-2026-09-26d-filter-walk"></a>
- [Reviewed 2026-09-26d filter-walk handback — a key-owned filter is walked against the key, and the walk reads every spec in the body](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md#inbound-2026-09-26d-filter-walk)
<a id="inbound-2026-09-26d-marked-read"></a>
- [Reviewed 2026-09-26d marked-read handback — a `$`-marked read in a body is judged as the rule's own read](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md#inbound-2026-09-26d-marked-read)
<a id="inbound-2026-09-26d-reference-set"></a>
- [Reviewed 2026-09-26d reference-set handback — the post-parse error-field gates count only references outside every filter body and marked ones inside](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26d-THROUGH-2026-09-26e.md#inbound-2026-09-26d-reference-set)

### Inbound 2026-09-26b and 2026-09-26c handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-26c-joined-comparison"></a>
- [Reviewed 2026-09-26c joined-comparison handback — a field copied into a field draws the class its kind pair draws in a comparison, and a Boolean field source leaves the constant ladder](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md#inbound-2026-09-26c-joined-comparison)
<a id="inbound-2026-09-26c-target-read"></a>
- [Reviewed 2026-09-26c target-read and member-order handback — a partially known Date or raw String read draws its read class alone, and a computation's members answer in the order A12 joins them](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md#inbound-2026-09-26c-target-read)
<a id="inbound-2026-09-26c-star-above-index"></a>
- [Reviewed 2026-09-26c star-above-index handback — a star on an unindexed repetition above the index group is refused even from a rule that iterates that level](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md#inbound-2026-09-26c-star-above-index)
<a id="inbound-2026-09-26b-dispositions"></a>
- [Reviewed 2026-09-26b field-value read handback — `SPEC-2026-09-25-09`, `-25-10` and `-26-01` confirmed on the peer's carrier](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md#inbound-2026-09-26b-dispositions)
<a id="inbound-2026-09-26b-entity-list-category"></a>
- [Reviewed 2026-09-26b entity-list category handback — an Enumeration's category is refused by every entity list whose carrier refuses one, and a category behind a group draws the group class](archived/SOURCES-INBOUND-HANDBACKS-2026-09-26b-THROUGH-2026-09-26c.md#inbound-2026-09-26b-entity-list-category)

### Inbound 2026-09-25i and 2026-09-26 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25i-key-addressing"></a>
- [Reviewed 2026-09-25i key-addressing handback — a key addresses only its index group's level, a defective key answers first, and the key's own crossing draws the semantic-index class](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-25i-key-addressing)
<a id="inbound-2026-09-25i-literal-key"></a>
- [Reviewed 2026-09-25i literal-key handback — a quoted key is judged by the index field, and an unquoted digit sequence is an entity name](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-25i-literal-key)
<a id="inbound-2026-09-25i-rule-iteration"></a>
- [Reviewed 2026-09-25i rule-iteration handback — the level a rule iterates addresses a scalar slot's read, from the declaring group or the error field's](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-25i-rule-iteration)
<a id="inbound-2026-09-25i-keyed-duplicate"></a>
- [Reviewed 2026-09-25i keyed-duplicate handback — a keyed group and a keyed field of it repeat only under one key](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-25i-keyed-duplicate)
<a id="inbound-2026-09-25i-enum-source"></a>
- [Reviewed 2026-09-25i enumeration-source handback — a starred source meets the star gate after its category and before the target's source gate, and a climbing source is judged as a local one](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-25i-enum-source)
<a id="inbound-2026-09-26-climbing-read"></a>
- [Reviewed 2026-09-26 climbing-read handback — a climbing read is judged at the level it lands on](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-26-climbing-read)
<a id="inbound-2026-09-26-index-key-shape"></a>
- [Reviewed 2026-09-26 index-key handback — a constant key meets its index field's value validation as a shape test, one rule per kind](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md#inbound-2026-09-26-index-key-shape)

### Inbound 2026-09-25g and 2026-09-25h handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25g-value-list-order"></a>
- [Reviewed 2026-09-25g value-list handback — `SPEC-2026-09-25-08` confirmed, and the construct's five gate positions measured](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25g-value-list-order)
<a id="inbound-2026-09-25g-date-class"></a>
- [Reviewed 2026-09-25g ordering handback — `SPEC-2026-09-25-07` confirmed with the Date on either side](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25g-date-class)
<a id="inbound-2026-09-25g-field-value-read"></a>
- [Reviewed 2026-09-25g field-value read handback — `SPEC-2026-09-25-06` confirmed, and a filter's body refuses a repeatable group it does not iterate](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25g-field-value-read)
<a id="inbound-2026-09-25g-rounding-mode"></a>
- [Reviewed 2026-09-25g rounding-mode handback — `RoundDown` beside `!=` is refused](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25g-rounding-mode)
<a id="inbound-2026-09-25g-banded-rounding"></a>
- [Reviewed 2026-09-25g banded-rounding handback — a banded computation's mode rounds to zero places, `Exact` floors to the target's digits, and the validation compares the operation as authored](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25g-banded-rounding)
<a id="inbound-2026-09-25g-keyed-group"></a>
- [Reviewed 2026-09-25g keyed-group handback — a keyed group's operand reads the selected row's cells, a lower repeatable level included](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25g-keyed-group)
<a id="inbound-2026-09-25h-category-index-relevance"></a>
- [Reviewed 2026-09-25h category handback — a category read over an index cell the document makes unavailable tracks the value read](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25g-THROUGH-2026-09-25h.md#inbound-2026-09-25h-category-index-relevance)

### Inbound 2026-09-25e and 2026-09-25f handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25f-value-list-base-type"></a>
- [Reviewed 2026-09-25f base-type handback — `SPEC-2026-09-25-05` confirmed on every pair it names](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25f-value-list-base-type)
<a id="inbound-2026-09-25f-field-value-read"></a>
- [Reviewed 2026-09-25f field-value read handback — the bracket asks its gates as it closes, wherever it stands, and a scalar value list's members ask theirs during the parse](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25f-field-value-read)
<a id="inbound-2026-09-25f-generated-text"></a>
- [Reviewed 2026-09-25f generated-text handback — a computation's members are parsed inside the one condition generated from them](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25f-generated-text)
<a id="inbound-2026-09-25f-bare-entity"></a>
- [Reviewed 2026-09-25f bare-entity handback — a bare entity stands only where an operator's argument is typed as one](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25f-bare-entity)
<a id="inbound-2026-09-25e-below-star-placement"></a>
- [Reviewed 2026-09-25e placement handback — the below-star placement holds on every carrier `SPEC-2026-09-25-02` names](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25e-below-star-placement)
<a id="inbound-2026-09-25e-sum-of-products-reach"></a>
- [Reviewed 2026-09-25e `SumOfProducts` handback — the operator's chain keeps its order from outside its fields' groups, and a star on a bound level counts](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25e-sum-of-products-reach)
<a id="inbound-2026-09-25e-value-list-base-type"></a>
- [Reviewed 2026-09-25e base-type handback — the value-list quantifiers ask one base type ahead of their kind gate, the temporal kinds sharing one and a custom declaration String's](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25e-value-list-base-type)
<a id="inbound-2026-09-25e-comparison-arm-order"></a>
- [Reviewed 2026-09-25e arm-order handback — a comparison between two fields answers its kind arms in a fixed order, and only the first draws a class](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25e-THROUGH-2026-09-25f.md#inbound-2026-09-25e-comparison-arm-order)

### Inbound 2026-09-25b and 2026-09-25c handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25b-index-type-table"></a>
- [Reviewed 2026-09-25b index-type handback — which two index kinds pair is a measured table, and a marked filter reference draws the class its read draws outside the filter](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25b-index-type-table)
<a id="inbound-2026-09-25b-condition-class-order"></a>
- [Reviewed 2026-09-25b class-order handback — a refused condition text draws the class raised first, an operator's gate as soon as its call is read](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25b-condition-class-order)
<a id="inbound-2026-09-25b-condition-positions"></a>
- [Reviewed 2026-09-25b position handback — parentheses group conditions only, and a sign stands on a number literal alone](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25b-condition-positions)
<a id="inbound-2026-09-25b-computation-texts"></a>
- [Reviewed 2026-09-25b computation-text handback — the suppression member's class answers first, a parse-time class erases the calculation module's, and a filter's gate answers for its own predicates](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25b-computation-texts)
<a id="inbound-2026-09-25b-message"></a>
- [Reviewed 2026-09-25b message handback — the unreferenced-target class withholds the error-text checker's classes, and an answered locale leaves `RULE_HAS_NO_ERRORTEXT` to the other](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25b-message)
<a id="inbound-2026-09-25b-joint-level-slots"></a>
- [Reviewed 2026-09-25b joint-level handback — a field read on a jointly iterated level meets its scalar slot's own gate](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25b-joint-level-slots)
<a id="inbound-2026-09-25c-gate-raise-points"></a>
- [Reviewed 2026-09-25c gate-order handback — a gate is raised where the production that owns it ends](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25c-gate-raise-points)
<a id="inbound-2026-09-25c-form-keyword"></a>
- [Reviewed 2026-09-25c form-keyword handback — a form construct's class is raised on its keyword wherever a condition opens](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25c-form-keyword)
<a id="inbound-2026-09-25c-key-filter"></a>
- [Reviewed 2026-09-25c key-filter handback — a `Having` after a field-valued index key is the key's filter](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25c-key-filter)
<a id="inbound-2026-09-25c-filter-body"></a>
- [Reviewed 2026-09-25c filter-body handback — a body's comparison draws its outside class, and the filter's chain is raised at two points around the body](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25c-filter-body)
<a id="inbound-2026-09-25c-calculation-stages"></a>
- [Reviewed 2026-09-25c calculation handback — the calculation module asks its stages in order, its rounding mode judges each alternative, and a variant-filtered computation is no cycle node](archived/SOURCES-INBOUND-HANDBACKS-2026-09-25b-THROUGH-2026-09-25c.md#inbound-2026-09-25c-calculation-stages)

### Inbound 2026-09-24c through 2026-09-25 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-25-fixed-group-star"></a>
- [Reviewed 2026-09-25 fixed-group-star handback — a star on a fixed group draws `MVK_INVALID_WILDCARD` alone at every position measured, and of two defects the one read first answers](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-fixed-group-star)
<a id="inbound-2026-09-25-message-withheld"></a>
- [Reviewed 2026-09-25 message-withholding handback — a refused DSL member withholds the error-text checker's classes, the message's presence classes stand, and only a declared locale's last entry is examined](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-message-withheld)
<a id="inbound-2026-09-25-keyed-group-walk"></a>
- [Reviewed 2026-09-25 keyed group-walk handback — the order-aware walk over a keyed group's fields stops at the first filled cell, and a String index is decided as a Number index is](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-keyed-group-walk)
<a id="inbound-2026-09-25-bare-group-placement"></a>
- [Reviewed 2026-09-25 bare-group placement handback — a bare repeatable group operand places its refusal as a field read does, and `AllGroupsFilled` joins the below-star carriers](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-bare-group-placement)
<a id="inbound-2026-09-25-comment-terminators"></a>
- [Reviewed 2026-09-25 comment handback — a `;;` comment admits every character but the two line terminators, and a lone carriage return ends it](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-comment-terminators)
<a id="inbound-2026-09-25-operator-gates-wait"></a>
- [Reviewed 2026-09-25 operator-gates handback — every gate of an operator's own waits for its operands to be read](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-operator-gates-wait)
<a id="inbound-2026-09-25-parallel-index-gates"></a>
- [Reviewed `kf371` route table — a level beside the error field's group meets its index gates one level at a time, outermost first](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-25-parallel-index-gates)
<a id="inbound-2026-09-24e-misplaced-star"></a>
- [Reviewed 2026-09-24e misplaced-star handback — a star on a field or fixed group draws `MVK_INVALID_WILDCARD` alone, even where the same reference leaves a repeatable level unstarred](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24e-misplaced-star)
<a id="inbound-2026-09-24e-nested-partial-star"></a>
- [Reviewed 2026-09-24e nested partial-star handback — a star that leaves one nested level bare counts as the unstarred read, ahead of the unreferenced-target class](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24e-nested-partial-star)
<a id="inbound-2026-09-24e-message-withheld"></a>
- [Reviewed 2026-09-24e message-withholding handback — a message is judged only beside a sound DSL member, post-parse classes included, and a name or error-code class does not withhold it](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24e-message-withheld)
<a id="inbound-2026-09-24e-filter-leaf"></a>
- [Reviewed 2026-09-24e filter-leaf handback — a `Having` filter's own leaf and a semantic index's value half are not per-row reads for containment](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24e-filter-leaf)
<a id="inbound-2026-09-24d-star-containment"></a>
- [Reviewed 2026-09-24d star-containment handback — containment, not binding, answers a per-row read into a written field outside the declaring group, and the written field's position names the walk's class](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24d-star-containment)
<a id="inbound-2026-09-24d-mixed-group-count"></a>
- [Reviewed 2026-09-24d mixed group-count handback — a partial `NumberOfFilledGroups` list mixing a starred and a fixed operand is undecided when either operand is](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24d-mixed-group-count)
<a id="inbound-2026-09-24c-path-walk"></a>
- [Reviewed 2026-09-24c path-walk handback — an up-step stands only in a relative path's leading run, and the short-name fallback answers a relative path's first segment alone](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24c-path-walk)
<a id="inbound-2026-09-24c-field-slot"></a>
- [Reviewed 2026-09-24c field-slot handback — a group in `FieldFilled` or `FieldNotFilled` meets the walk, then a root's class, then the kind gate, and a star follows them](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24c-field-slot)
<a id="inbound-2026-09-24c-group-operand-walk"></a>
- [Reviewed 2026-09-24c group-operand walk handback — an unstarred repeatable group draws the missing star ahead of every carrier gate, and a repeatable root is walked like any group](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24c-THROUGH-2026-09-25.md#inbound-2026-09-24c-group-operand-walk)

### Inbound 2026-09-24 and 2026-09-24b handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md) when this hub neared its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-24b-keyed-partial-read"></a>
- [Reviewed 2026-09-24b keyed partial-read handback — partial validation judges a keyed read at the coordinate its key resolves to](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-keyed-partial-read)
<a id="inbound-2026-09-24b-lexer-and-blank-text"></a>
- [Reviewed 2026-09-24b lexer and blank-text handback — whitespace is the lexer's five characters, the suppression list is parsed as preamble text, and member blankness follows `isWhitespace`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-lexer-and-blank-text)
<a id="inbound-2026-09-24b-category-read-poison"></a>
- [Reviewed 2026-09-24b category-read poison handback — a computation's category read of a malformed Enumeration cell poisons like its value read](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-category-read-poison)
<a id="inbound-2026-09-24b-kf463-validation"></a>
- [Reviewed 2026-09-24b `kf463` validation handback — a below-star `Seal` counts by its decided content, a malformed-only one leaves the count unavailable, and the extent is per operand](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-kf463-validation)
<a id="inbound-2026-09-24b-kf464-partial-group-extent"></a>
- [Reviewed 2026-09-24b `kf464` first-table handback — a field-expanding aggregate over a starred group is evaluable under partial validation exactly when every field it contains is](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-kf464-partial-group-extent)
<a id="inbound-2026-09-24b-kf464-partial-group-count"></a>
- [Reviewed 2026-09-24b `kf464` second-table handback — `NumberOfFilledGroups` under partial validation is a four-step walk over the counted group's own instances](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-kf464-partial-group-count)
<a id="inbound-2026-09-24b-dispositions"></a>
- [Reviewed 2026-09-24b dispositions handback — three outbound entries accepted, and the root gate reaches every value-list quantifier and either side of the field-read spelling](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24b-dispositions)
<a id="inbound-2026-09-24-ancestor-starred-group-count"></a>
- [Reviewed 2026-09-24 ancestor-starred group-count handback — a fixed group below a starred level is a sole `NumberOfFilledGroups` operand, and it counts filled instances only](archived/SOURCES-INBOUND-HANDBACKS-2026-09-24-THROUGH-2026-09-24b.md#inbound-2026-09-24-ancestor-starred-group-count)

### Inbound 2026-09-23 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md) when this hub crossed its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-23d-grandparent-fill-and-malformed-key"></a>
- [Reviewed 2026-09-23 grandparent-fill and malformed-key handback — the cascade fill reaches depth two, and a malformed field-valued key is unknown or poison on every keyed consumer](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md#inbound-2026-09-23d-grandparent-fill-and-malformed-key)
<a id="inbound-2026-09-23c-computation-cascade-reads"></a>
- [Reviewed 2026-09-23 computation-cascade handback — a computed field's stored value is read by nothing inside one call, and a precondition has no row gate](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md#inbound-2026-09-23c-computation-cascade-reads)
<a id="inbound-2026-09-23b-entity-list-operand-reads"></a>
- [Reviewed 2026-09-23 entity-list operand-read handback — an unreadable operand answers first across the family, and the date walk sits behind the list gates](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md#inbound-2026-09-23b-entity-list-operand-reads)
<a id="inbound-2026-09-23-first-filled-gate-positions"></a>
- [Reviewed 2026-09-23 `FirstFilledValue` gate-position handback — operand reads first, then duplicates, root and arity, then Confirm wherever it stands](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md#inbound-2026-09-23-first-filled-gate-positions)
<a id="inbound-2026-09-23-entity-list-root-group-gate"></a>
- [Reviewed 2026-09-23 entity-list root-group gate — a Kernel gate the shared Lean shape did not ask](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md#inbound-2026-09-23-entity-list-root-group-gate)
<a id="inbound-2026-09-22e-first-filled-gate-order"></a>
- [Reviewed 2026-09-23 `FirstFilledValue` gate-order handback — duplicates, then Confirm, then one type over the expanded fields, and a Kernel row behind a Lean lock](archived/SOURCES-INBOUND-HANDBACKS-2026-09-23.md#inbound-2026-09-22e-first-filled-gate-order)

### Inbound 2026-09-22 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-22.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-22.md) when this hub crossed its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-22d-first-filled-cross-kind"></a>
- [Reviewed 2026-09-22 `FirstFilledValue` cross-kind handback — the date-bearing pairs measured at a date format, and a bound this project had relayed withdrawn](archived/SOURCES-INBOUND-HANDBACKS-2026-09-22.md#inbound-2026-09-22d-first-filled-cross-kind)
<a id="inbound-2026-09-22-temporal-category"></a>
- [Reviewed 2026-09-22 temporal-category handback — the four-member category measured, and a clause that was careful turned into an overclaim by the arrival of its own evidence](archived/SOURCES-INBOUND-HANDBACKS-2026-09-22.md#inbound-2026-09-22-temporal-category)
<a id="inbound-2026-09-22-dispositions"></a>
- [Reviewed 2026-09-22 dispositions handback — the whole pending queue answered, three clauses qualified, and both instrument asks implemented](archived/SOURCES-INBOUND-HANDBACKS-2026-09-22.md#inbound-2026-09-22-dispositions)

### Inbound 2026-09-21 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-21.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-21.md) when this hub approached its size ceiling. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-21b-corrections"></a>
- [Reviewed 2026-09-21b reply handback — both contrary entries accepted, our own replacement reading corrected, and four clauses changed](archived/SOURCES-INBOUND-HANDBACKS-2026-09-21.md#inbound-2026-09-21b-corrections)
<a id="inbound-2026-09-21-corrections"></a>
- [Reviewed 2026-09-21 corrections handback — 163 new peer findings triaged, sixteen clauses corrected, one Lean precedence defect found, and two of their rows refuted](archived/SOURCES-INBOUND-HANDBACKS-2026-09-21.md#inbound-2026-09-21-corrections)

### Inbound 2026-09-07 and 2026-09-08 handbacks

Moved to [`archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md`](archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md) when this hub reached its size ceiling a second time. The anchors below keep every existing `SOURCES.md#inbound-…` citation resolving.

<a id="inbound-2026-09-08-corrections"></a>
- [Reviewed 2026-09-08 corrections handback — three entries confirmed, one of their titles refuted, and the observation hash preimage changed](archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md#inbound-2026-09-08-corrections)
<a id="inbound-2026-09-08-instrument"></a>
- [Reviewed 2026-09-08 instrument handback — malformed model input reclassified, and one authoring restriction removed that opened a refusal class](archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md#inbound-2026-09-08-instrument)
<a id="inbound-2026-09-08"></a>
- [Reviewed 2026-09-08 handback — four pending entries answered, three declaration knobs made authorable, and two kernel derivations opened](archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md#inbound-2026-09-08)
<a id="inbound-2026-09-07-dispositions"></a>
- [Reviewed 2026-09-07 dispositions — nine entries answered at one revision, one of ours refuted, one assumption discharged, and two rows sent unasked](archived/SOURCES-INBOUND-HANDBACKS-2026-09-07-THROUGH-2026-09-08.md#inbound-2026-09-07-dispositions)

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
<a id="src-string-integer-source-scale-suppression"></a>
- [String integer-source computation scale suppression, measured locally 2026-09-09](sources/computation-placement-and-constant-probes.md#src-string-integer-source-scale-suppression)
<a id="src-date-range-bound-component-scale-suppression"></a>
- [DateRange component assignment scale and computation suppression, measured locally 2026-09-09](sources/temporal-and-message-probes.md#src-date-range-bound-component-scale-suppression)
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

<a id="src-repetition-numeric-source-kinds"></a>
- [Mixing with `CurrentRepetition` does not narrow a repeatable Number target's admitted source kinds](sources/group-and-iteration-probes.md#src-repetition-numeric-source-kinds)

<a id="src-repetition-operand-partial-relevance"></a>
- [`CurrentRepetition` is structural for partial-validation relevance too, so a rule that reads it alone fires under a coverage that suppresses its field-reading neighbour](sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance)

<a id="src-ancestor-declared-repetition-computation"></a>
- [A computation's declaring group selects neither its iteration nor its values; containment of the target is the only thing it decides](sources/group-and-iteration-probes.md#src-ancestor-declared-repetition-computation)

<a id="src-repetition-aggregate-operand-scope"></a>
- [An aggregate operand answers the calculated-field ban through a star, and answers no scope rule at all](sources/group-and-iteration-probes.md#src-repetition-aggregate-operand-scope)

<a id="src-repetition-source-kinds-runtime"></a>
- [Every widened source beside a repetition operand reads at its own declaration's scope in the reading row](sources/group-and-iteration-probes.md#src-repetition-source-kinds-runtime)
<a id="src-currentrepetition-operand-carriers"></a>
- [The operand is an ordinary Number expression wherever one is legal, while `$` is filter-only by site and no aggregate accepts it](sources/group-and-iteration-probes.md#src-currentrepetition-operand-carriers)

<a id="src-filter-repetition-reference-reads-its-path"></a>
- [A `CurrentRepetition` leaf answers both filter gates through its path's repeatable scope, so a nonrepeatable group under the star satisfies the scope gate alone](sources/having-filter-probes.md#src-filter-repetition-reference-reads-its-path)

<a id="src-fixed-repetition-having"></a>
- [A fixed group's filter index is one while its path still controls binding](sources/having-filter-probes.md#src-fixed-repetition-having)

<a id="src-filter-reference-above-the-star"></a>
- [A level above the star but still on the operand's path is scope-gated and rescuable, not iteration-prohibited](sources/having-filter-probes.md#src-filter-reference-above-the-star)

<a id="src-parameter-token-versus-group-declaration-alphabet"></a>
- [The parameter's name token is wider than any group may be named, and a quoted segment is refused where the bare spelling reaches lookup](sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet)

<a id="src-terminal-bundle-on-the-computation-carrier"></a>
- [The parameter terminal bundle is shared with the computation message carrier, where `RuleGroup` names the computation's own group](sources/message-and-pointer-probes.md#src-terminal-bundle-on-the-computation-carrier)

<a id="src-name-position-index-terminal"></a>
- [`index(...)` is a live name-position terminal with three refusal codes of its own, and the group position has no index syntax at all](sources/message-and-pointer-probes.md#src-name-position-index-terminal)
<a id="src-message-template-character-repertoire"></a>
- [The rule-message template's repertoire is the BMP rather than printable ASCII, its control class covers the C1 block and the invisible format characters, the ASCII bound belongs to a parameter body alone, and the name position's condition-reference gate is `INVALID_FIELD`](sources/message-and-pointer-probes.md#src-message-template-character-repertoire)

<a id="src-message-repertoire-co-reporting"></a>
- [Rule-message repertoire findings coexist with named failures; full diagnostic lists correct the priority inferred from code-only observations](sources/message-and-pointer-probes.md#src-message-repertoire-co-reporting)

<a id="src-message-category-gate-order"></a>
- [Rule-message entity and membership/index failures precede an empty category name](sources/message-and-pointer-probes.md#src-message-category-gate-order)

<a id="src-message-parameter-surface-and-iteration-gates"></a>
- [The rule-message parameter surface read off its own grammar: the value suffix's second gate is a field declaration (`INVALID_NO_VALUE_VALIDATION`), `$Entity.Vordruckzeile$` skips the condition-membership gate, `$#RootGroup$` is gated on parallel iteration, the group position takes a matching semantic-index key, and the index terminal's cross-declaration consistency family is reachable](sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates)

<a id="src-index-terminal-refusal-classes"></a>
- [The `index(...)` terminal's complete refusal-class set: `->Category` admitted on an Enumeration index field with its own `INVALID_CATEGORY`, multiplicity refused `INVALID_INDEX_FIELD_AMBIGUOUS`, and a cross-check against the rule's own condition refusing a keyed or starred reference `INVALID_INDEX_FIELD_REP_ITER`](sources/message-and-pointer-probes.md#src-index-terminal-refusal-classes)
<a id="src-starred-group-value-count-classes"></a>
- [A starred group naming nothing answers in the segment order on the filled-field and value-count carriers too, and a fixed group below a star is admitted on every one of them](sources/path-resolution-class-probes.md#src-starred-group-value-count-classes)
<a id="src-pattern-and-key-resolver-classes"></a>
- [A pattern comparison's field and a `RepetitionNotUnique` key draw the shared resolver classes, and a field read from the rule that iterates it is admitted on the pattern and group-list carriers](sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)
<a id="src-group-operand-resolution-classes"></a>
- [A group operand that does not resolve draws the class of the segment that missed, fixed or starred](sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)
<a id="src-short-name-ambiguity-every-carrier"></a>
- [A bare name that matches several fields model-wide draws `MVK_FIELDNAME_NOT_UNIQUE` on every carrier asked, a computation included](sources/path-resolution-class-probes.md#src-short-name-ambiguity-every-carrier)
<a id="src-starred-path-segment-order"></a>
- [A starred path is judged segment by segment, so a star on a nonrepeatable segment outranks a later miss and a miss outranks its own star](sources/path-resolution-class-probes.md#src-starred-path-segment-order)
<a id="src-resolver-failure-classes-every-carrier"></a>
- [A field name that does not resolve draws one of three classes on every carrier asked, and the root class turns on the first segment](sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)
<a id="src-entity-list-kind-empty-and-root-carriers"></a>
- [`Sum` refuses a String in every position and form, an empty starred group answers ahead of the group-list star gate, and the root gate reaches the value list and a computation](sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)
<a id="src-value-list-slot-kind-set"></a>
- [The String-literal value list's slot gate is one class over seven kinds and does not read the slot's shape, with NUMBER inside the admitted set](sources/static-admission-and-class-probes.md#src-value-list-slot-kind-set)
<a id="src-variant-filter-declaration-omission"></a>
- [An `ONLY` variant filter removes a declaration from the model, so a broken rule reports clean while a filtered field breaks every reference to it](sources/static-admission-and-class-probes.md#src-variant-filter-declaration-omission)
<a id="src-comparison-constant-gate-immediacy"></a>
- [The comparison's constant gate asks whether both sides are immediate written-out literals, not whether either reads a cell](sources/static-admission-and-class-probes.md#src-comparison-constant-gate-immediacy)

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

<a id="src-value-list-base-type-cross-pairs"></a>
- [Every cross pair of base types the value-list quantifier's homogeneity gate was asked draws `MVK_VARYING_TYPES_NOT_ALLOWED`, the token families in both orders on both sides and the boolean kinds in both orders against a literal](sources/static-admission-and-class-probes.md#src-value-list-base-type-cross-pairs)
<a id="src-field-value-read-grid"></a>
- [The field-value read's gates reach a root group, a filter body's iterated level, a value-list member, a copied computation operand and a `Today` comparison, and a partner whose read fails answers ahead of an ordering's kind class](sources/static-admission-and-class-probes.md#src-field-value-read-grid)
<a id="src-field-value-read-carriers"></a>
- [The field-value read's gates answer ahead of an arithmetic operator's class, on a computation's operand writing a String, an Enumeration, a Time or a Number, and on a category read](sources/static-admission-and-class-probes.md#src-field-value-read-carriers)
<a id="src-field-value-read-remaining-sites"></a>
- [A pattern comparison's field and a DateRange comparison's sides answer the field-value read's classes, a scalar membership's group subject waits for its members, a declaring group's own group takes no short-name fallback, and a computation reading a repeatable group draws the missing-star class](sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)
<a id="src-field-value-read-predictions"></a>
- [A field an operator names as a parameter asks the group gate alone, a category read of a field declaring no Enumeration draws `MVK_NO_ENUMERATION` on every carrier measured, entity lists included, and a repeatable or parallel computation target reads as a nonrepeatable one does, its own group drawing the group class](sources/static-admission-and-class-probes.md#src-field-value-read-predictions)
<a id="src-value-list-cross-list-repeat-order"></a>
- [A reference repeated across a value-list quantifier's two lists is asked after its base-type and kind gates, and one repeated within the field list before them](sources/static-admission-and-class-probes.md#src-value-list-cross-list-repeat-order)
<a id="src-ordering-date-class-reads-the-pair"></a>
- [An ordering's date-kind class reads the pair: a Date on either side of a Number, constant or field, draws `MVK_INVALID_COMPARE_TO_DATE`](sources/static-admission-and-class-probes.md#src-ordering-date-class-reads-the-pair)
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
<a id="src-parser-static-legality-sweep"></a>
- [Ten condition-level refusal classes named in one generated sweep: the type/arity gates `MVK_NO_STRING_OR_NUMBER_FOR_ADD`, `MVK_INVALID_TYPE_FOR_TOLERANCE_OP`, `MVK_PARAMSIZE_INVALID1`, `MVK_NO_FIELDS_ALLOWED`, the category twins `MVK_CATEGORY_UNKOWN` and `MVK_NO_ENUMERATION`, the constant-pair gate `MVK_INVALID_COMPARE_TO_CONST`, and the filter star gate `MVK_WILDCARDS_REQUIRED`](sources/diagnostic-class-vocabulary-and-sweeps.md#src-parser-static-legality-sweep)

<a id="src-typedef-resolves-to-base-kind"></a>
- [A typedef field is its base kind at three independent gates, which makes `spec/01`'s model-expansion exclusion measured rather than assumed](sources/static-admission-and-class-probes.md#src-typedef-resolves-to-base-kind)
<a id="src-first-filled-reads-the-format-string"></a>
- [The four entity-list carriers split two-and-two on one field pair: the extrema and the distinct count read the component set, `FirstFilledValue` and `FieldValuesNotUnique` read the format string](sources/static-admission-and-class-probes.md#src-first-filled-reads-the-format-string)
<a id="src-equal-set-spelling-families-carrier-split"></a>
- [The two-and-two carrier split holds across all three equal-set spelling families, the extrema ignore component order as well as spelling, and a declared Base Year changes none of it](sources/static-admission-and-class-probes.md#src-equal-set-spelling-families-carrier-split)
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
<a id="src-entity-list-sole-operand-arity"></a>
- [`FirstFilledValue`'s sole-operand rule is the disjunction its own Kernel message states — more than one field **or** at least one group — while the entity-valued value list admits a sole field on each side](sources/static-admission-and-class-probes.md#src-entity-list-sole-operand-arity)

<a id="src-notind-declaration-properties-are-mapping-provenance"></a>
- [The six `@NotInD` declaration properties never reach validation codegen or the runtime, the structural-mapping tool is their sole semantic consumer and overrides the format there, and the annotation's own no-effect Javadoc is falsified by its use on the decimal separator](sources/diagnostic-class-vocabulary-and-sweeps.md#src-notind-declaration-properties-are-mapping-provenance)

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
<a id="src-group-field-fill-declared-slots"></a>
- [Field-group quantifiers retain declared slots and bound-parent capacity](sources/group-list-and-capacity-probes.md#src-group-field-fill-declared-slots)
<a id="src-computation-star-binding-gate"></a>
- [A repeatable level a star leaves unstarred must be bound: below the first star it draws the missing-star class on every carrier measured, and above it a fixed-target computation's class follows where its target lies](sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)
<a id="src-validation-below-star-placement"></a>
- [Below the first star the error field places the refusal on twenty-two validation star carriers: containment from a rule group it lies outside, the missing star from one it lies in](sources/group-list-and-capacity-probes.md#src-validation-below-star-placement)
<a id="src-validation-below-star-placement-kinds"></a>
- [The same placement holds on the token, temporal, DateRange, Boolean, Enumeration and `SumOfProducts` carriers, on either value-list side, on a group under a filled-field carrier and on a filtered star](sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)
<a id="src-walk-batch-reading-scope"></a>
- [The error field's scope binds a validation read's levels only when the error field lies at or below the rule group, and a computation places its refusal by its target](sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)
<a id="src-ancestor-starred-group-count-computation"></a>
- [`NumberOfFilledGroups` counts a fixed group below a star on the computation arm by content per in-capacity instance, and a computation reading a malformed-only operand group emits no implicit message](sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation)
<a id="src-below-star-group-computation"></a>
- [A fixed group below a star is admitted and computed on the expansion account on the computation arm too](sources/group-list-and-capacity-probes.md#src-below-star-group-computation)
<a id="src-below-star-group-runtime"></a>
- [A fixed group below a star counts its own fields in every reopened in-capacity row, moves until every declared slot below the star is filled, and a group operand's value count stays growable while a reopened row is missing](sources/group-list-and-capacity-probes.md#src-below-star-group-runtime)
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
<a id="src-dynamic-enumeration-legality"></a>
- [Dynamic-enumeration derivation refuses in four ordered stages, eleven of twelve classes attributed to one witness rule each](sources/rule-set-meta-information.md#src-dynamic-enumeration-legality)

<a id="src-index-and-sort-field-declaration"></a>
- [A group's index and sort nominations share one cascade](sources/model-structure-and-declaration-probes.md#src-index-and-sort-field-declaration)

<a id="src-temporal-constructor-operand-positions"></a>
- [A temporal constructor checks each operand position separately, and two classes distinguish a misplaced extractor from an inadmissible one](sources/static-admission-and-class-probes.md#src-temporal-constructor-operand-positions)

<a id="src-form-condition-constructs"></a>
- [The form-level constructs are German-only, so an A12 model's diagnostic for them depends on its condition language](sources/diagnostic-class-vocabulary-and-sweeps.md#src-form-condition-constructs)

<a id="src-generated-rule-identity"></a>
- [The four auto-generated rules carry three projections that partition them differently](sources/model-structure-and-declaration-probes.md#src-generated-rule-identity)

<a id="src-entity-container-integrity"></a>
- [The per-entity integrity walk reads the entity's name rather than its identifier, and its first four stages hide the whole subtree](sources/model-structure-and-declaration-probes.md#src-entity-container-integrity)
<a id="src-error-target-declaration"></a>
- [A rule's error field draws two different iteration classes depending on how its condition reaches it, and the class turns on the reference partition rather than on any star in the text](sources/model-structure-and-declaration-probes.md#src-error-target-declaration)
<a id="src-index-group-resolution"></a>
- [Exactly one index group may govern a reference, and the walk that finds it examines only the innermost one's declared count](sources/model-structure-and-declaration-probes.md#src-index-group-resolution)
<a id="src-rule-change-propagation"></a>
- [The Kernel's own rule-change service declines to propagate a move in an A12 model, and an independent implementation performs that propagation soundly](sources/model-structure-and-declaration-probes.md#src-rule-change-propagation)
<a id="src-repeatability-restriction"></a>
- [A rule counting repetitions is read backwards as a repeatability restriction, and the pass that does so is reached by neither available gate](sources/model-structure-and-declaration-probes.md#src-repeatability-restriction)
<a id="src-error-text-row-parameter"></a>
- [An error text's row-index parameter is refused when the condition reaches its group only through a star, and the rule is existential over the condition's references](sources/model-structure-and-declaration-probes.md#src-error-text-row-parameter)
<a id="src-enumeration-category-constant"></a>
- [A literal compared against an enumeration's category is refused by a class the carrier chooses, and an enumeration value is not a category value](sources/static-admission-and-class-probes.md#src-enumeration-category-constant)
<a id="src-computation-normal-form-generation"></a>
- [An A12 computation's normalized condition is generated from its structure](sources/diagnostic-class-vocabulary-and-sweeps.md#src-computation-normal-form-generation)
<a id="src-table-enumeration-inertness"></a>
- [`ValueNotConsistent` is inert in an A12 document model](sources/diagnostic-class-vocabulary-and-sweeps.md#src-table-enumeration-inertness)
<a id="src-iteration-and-semantic-index-legality"></a>
- [Iteration, parallel iteration, and the semantic index share one two-layer static gate](sources/diagnostic-class-vocabulary-and-sweeps.md#src-iteration-and-semantic-index-legality)

<a id="src-over-limit-computation-target"></a>
- [An over-limit row receives no computed value](sources/group-list-and-capacity-probes.md#src-over-limit-computation-target)
<a id="src-boolean-first-filled-false-is-filled"></a>
- [`FirstFilledValue` selects a Boolean `false` because its filled predicate is presence, and an all-empty selection mints no outcome](sources/evaluation-and-application-routes.md#src-boolean-first-filled-false-is-filled)
<a id="src-first-filled-malformed-terminates-and-inventory-reports"></a>
- [A malformed `FirstFilledValue` source terminates the scan where an empty one falls through, and the eager operand inventory still reports the suffix the scan never read](sources/evaluation-and-application-routes.md#src-first-filled-malformed-terminates-and-inventory-reports)
<a id="src-mixed-chain-string-target-rejection"></a>
- [A rejected middle String remains visible through the Number and filtered Enumeration dependents](sources/evaluation-and-application-routes.md#src-mixed-chain-string-target-rejection)

<a id="src-firstfilled-string-boolean-runtime"></a>
- [Fixed and parent-local starred String and Boolean computation outcomes](sources/evaluation-and-application-routes.md#src-firstfilled-string-boolean-runtime)

<a id="src-first-filled-formal-branch-four-carriers"></a>
- [The `FirstFilledValue` formal-failure branch is the same on Boolean, DateFragment, Time and DateTime as on full Date, closing six of the seven carriers](sources/evaluation-and-application-routes.md#src-first-filled-formal-branch-four-carriers)
<a id="src-number-formal-cascade-code-axis-and-load-canonicalisation"></a>
- [The Number formal cascade's surfaced code and its message text are independent axes, and the canonical Document JSON load removes four refusals' preconditions](sources/evaluation-and-application-routes.md#src-number-formal-cascade-code-axis-and-load-canonicalisation)
<a id="src-index-iteration-and-constant-refusal-classes"></a>
- [Twenty-five parser refusal classes across the index, iteration, date-construction and constant families](sources/diagnostic-class-vocabulary-and-sweeps.md#src-index-iteration-and-constant-refusal-classes)
<a id="src-codegen-classes-reach-ordinary-authoring"></a>
- [The Kernel code-generation check family is reachable from ordinary authoring, because the consistency check runs the generator](sources/diagnostic-class-vocabulary-and-sweeps.md#src-codegen-classes-reach-ordinary-authoring)
<a id="src-unraised-diagnostic-vocabulary"></a>
- [Fifteen catalog keys the Kernel declares but never reports](sources/diagnostic-class-vocabulary-and-sweeps.md#src-unraised-diagnostic-vocabulary)
<a id="src-default-locale-message-bundles"></a>
- [The default-locale message bundle is a placeholder for every tool-time catalog](sources/diagnostic-class-vocabulary-and-sweeps.md#src-default-locale-message-bundles)
<a id="src-shipped-custom-field-type-vocabulary"></a>
- [The thirteen shipped custom field types and their thirty-six refusal keys](sources/diagnostic-class-vocabulary-and-sweeps.md#src-shipped-custom-field-type-vocabulary)
<a id="src-universal-value-formal-precheck"></a>
- [The type-independent formal pre-check every stored value passes](sources/static-admission-and-class-probes.md#src-universal-value-formal-precheck)
<a id="src-unraised-diagnostic-runtime-corroboration"></a>
- [A second carrier for the never-raised form-line diagnostic](sources/diagnostic-class-vocabulary-and-sweeps.md#src-unraised-diagnostic-runtime-corroboration)
<a id="src-date-range-list-iso-arity-and-fragment-suffix"></a>
- [The direct-field DateRange list executes at ISO/slash, recurses past three sources, reports a fragment suffix's formal failure, and renders an empty-separator `MM` target](sources/temporal-runtime-fold-probes.md#src-date-range-list-iso-arity-and-fragment-suffix)
<a id="src-yearless-extrema-base-year-ordering"></a>
- [The extrema order a yearless list under a declared Base Year on both strategies, and no document on such a model can say what they order on](sources/temporal-runtime-fold-probes.md#src-yearless-extrema-base-year-ordering)
<a id="src-extrema-component-omitting-fold"></a>
- [The extrema fold a component-omitting operand, yearless included, and order it correctly](sources/temporal-runtime-fold-probes.md#src-extrema-component-omitting-fold)
<a id="src-cross-kind-format-runtime-parser"></a>
- [The runtime text parser is the declared format's, not the declared kind's](sources/temporal-runtime-fold-probes.md#src-cross-kind-format-runtime-parser)
<a id="src-distinct-count-group-expansion-fold"></a>
- [A group operand's distinct count reaches its whole subtree at runtime, and an uninstantiated row contributes nothing](sources/temporal-runtime-fold-probes.md#src-distinct-count-group-expansion-fold)
<a id="src-distinct-count-time-bearing-fold"></a>
- [The distinct count folds a time-bearing operand too, and a TIME agrees with a time-only DATETIME](sources/temporal-runtime-fold-probes.md#src-distinct-count-time-bearing-fold)
<a id="src-distinct-count-component-omitting-fold"></a>
- [The distinct count folds a component-omitting date at its declared precision](sources/temporal-runtime-fold-probes.md#src-distinct-count-component-omitting-fold)
<a id="src-distinct-count-temporal-identity-both-strategies"></a>
- [The distinct count's temporal identity is the decoded date on both codegen strategies](sources/temporal-runtime-fold-probes.md#src-distinct-count-temporal-identity-both-strategies)
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

<a id="src-address-index-position-classes"></a>
- [The over-limit class follows the coordinate's position, and a repeatable root group draws the serial class throughout](sources/over-repetition-probes.md#src-address-index-position-classes)
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
- [A Date constant is classified by its own spelling and stored in the target's format](sources/temporal-constant-and-base-year-probes.md#src-date-constant-target-formatting)

<a id="src-date-constant-pre-1900-target"></a>
- [A Date constant reaches the target's opt-in pre-1900 policy after rendering](sources/temporal-constant-and-base-year-probes.md#src-date-constant-pre-1900-target)

<a id="src-constant-literal-family-gate"></a>
- [A bare constant's admission is gated by the target's declared format string, never its kind](sources/temporal-constant-and-base-year-probes.md#src-constant-literal-family-gate)
<a id="src-temporal-format-gate-not-component-sets"></a>
- [The temporal admission gate reads family and year agreement, never component sets](sources/temporal-constant-and-base-year-probes.md#src-temporal-format-gate-not-component-sets)
<a id="src-yearless-anchor-is-the-base-year"></a>
- [A yearless temporal literal resolves against the model's Base Year, while its calendar check ignores that year](sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year)
<a id="src-temporal-constant-literal-composition"></a>
- [The temporal literal vocabulary composes, and the Base Year gate reads year disagreement](sources/temporal-constant-and-base-year-probes.md#src-temporal-constant-literal-composition)

<a id="src-datetime-constant-zone-split"></a>
- [A DateTime constant is checked against two different zones at two different phases](sources/temporal-constant-and-base-year-probes.md#src-datetime-constant-zone-split)

<a id="src-component-omitting-date-formats"></a>
- [A component-omitting date target needs every component its format names, and the Base Year supplies the year](sources/temporal-constant-and-base-year-probes.md#src-component-omitting-date-formats)

<a id="src-base-year-yearless-store"></a>
- [A declared Base Year gates a yearless target's authoring and contributes nothing to its store](sources/temporal-constant-and-base-year-probes.md#src-base-year-yearless-store)
<a id="src-fixed-target-star-placement"></a>
- [Fixed computation target under a star operand: no placement gate](sources/computation-placement-and-constant-probes.md#src-fixed-target-star-placement)
<a id="src-unsuppressed-assignment-scale-reach"></a>
- [The unsuppressed assignment-scale overflow has no authored witness](sources/computation-placement-and-constant-probes.md#src-unsuppressed-assignment-scale-reach)
<a id="src-dotted-short-date-format"></a>
- [The dotted short date `dd.MM.` reads day-first and writes both dots, measured locally 2026-09-22](sources/temporal-and-message-probes.md#src-dotted-short-date-format)
<a id="src-valueless-outcome-minting-and-application"></a>
- [Two valueless outcomes leave the document identical and the result collection different, measured locally 2026-09-22](sources/evaluation-and-application-routes.md#src-valueless-outcome-minting-and-application)
<a id="src-errored-target-applied-state"></a>
- [An ERRORED computed target is cleared in the applied document and never carries its attempted payload, measured locally 2026-09-22](sources/evaluation-and-application-routes.md#src-errored-target-applied-state)
<a id="src-applied-document-over-limit-unobservable"></a>
- [The applied document of an over-capacity input cannot be observed, because the Kernel's own serializer refuses to write it, measured locally 2026-09-22](sources/evaluation-and-application-routes.md#src-applied-document-over-limit-unobservable)
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
<a id="src-join-poison-and-substitution"></a>
- [A malformed producer clears every Number join that reaches it, and a twelve-computation plan runs in dependency order, measured locally 2026-09-26](sources/evaluation-and-application-routes.md#src-join-poison-and-substitution)
<a id="src-two-level-repeatable-join"></a>
- [Poison and empty substitution cross repetition levels and rows by the same rule, measured locally 2026-09-26](sources/evaluation-and-application-routes.md#src-two-level-repeatable-join)
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
