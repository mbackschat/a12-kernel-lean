# Authoritative sources and drill routes

<a id="authoritative-sources--how-to-drill"></a>
<a id="authoritative-sources-how-to-drill"></a>

This hub and bounded [`sources/`](sources/) records own provenance: routes from semantic questions to authoritative kernel layers and maintained a12-dmkits knowledge. Specification, findings, implementation, evidence inventory and review history have separate owners.

Authority order is **[`../../a12-kernel`](../../a12-kernel) → project-owned [`../spec/`](../spec/) and Lean theory → [a12-dmkits](../../a12-rulekit)**. The real kernel is the behavioral oracle. The spec and Lean theory are this project’s working semantics-of-record. a12-dmkits is a peer clean-room implementation, source of maintained kernel-executing differentials, and knowledge corpus.

All kernel source routes below target kernel **30.8.1**, inspected at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. Read source to learn behavior; never link, call, ship, or transcribe it.

## Query contract

Start from the relevant [`spec/` clause](../spec/SEMANTICS-MAP.md), then:

1. identify the claim class with the engine routing rule;
2. use the clause table for the subsystem, then the [question-to-locus index](sources/kernel-loci.md#question-to-locus-index) for the exact decisive class, template, backing bean, method, or service;
3. follow a12-dmkits’ guard-checked [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) for its exhaustive prose/test/corpus inventory;
4. consult the [cross-layer packets](sources/cross-layer-routes.md#focused-cross-layer-packets) only for mechanisms not answered by one locus.

Search a topic with `rg -n '<topic>' docs/SOURCES.md docs/sources/`, then read only its linked record. Follow the family link directly; historical handbacks are consulted only for their provenance. Detailed claims and limits belong in the destination, so new navigation labels should name the topic briefly.

### How far to trust a 40-character revision receipt

**A revision citation certifies what was read when it was written, not that it still resolves.** Measured 2026-09-06: of 426 distinct 40-hex citations across `docs/` and `spec/`, **176 resolve in no local checkout**. Restricted to the live provenance owners — this file, `EVIDENCE.md`, the current ledger, and the `sources/` shards — **182 citations resolve at 80%**. The remaining dead ones concentrated in the since-deleted `archived/` directory, `LEAN-FORMALIZATION.md` and `PRODUCTION-RELEASE.md`, where they name frozen history or external repositories such as Cedar and Lean that no local checkout is expected to hold. Peer history is rewritten upstream and this repository's early history was rewritten too, so decay is the normal condition of an old receipt rather than evidence of a fabricated one.

Two consequences. A reader resolving an old citation and failing has learned nothing about the claim: re-derive it from the record's own `claim` and `separator` rows instead. And a *newly written* citation is different in kind — [`check-doc-hygiene.sh`](../scripts/check-doc-hygiene.sh) resolves every 40-hex string a commit range introduces that was not already in the tree, so a receipt is verified live at authoring time and never afterwards. Set `A12_REVISION_RANGE` to widen that range; the check reports `UNVERIFIABLE` rather than passing when a sibling checkout is absent.

Search reusable provenance entries with `rg -n '^<a id="src-' docs/sources/`, then read the selected record. Search the shard directly when updating a checkpoint. Add a route only when it is reusable by later work. A one-capsule source narrative belongs in working context and Git history, while a durable surprising mechanism belongs in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).

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

## Provenance checkpoint index

These links open the detailed source owners directly. Search their `src-` anchors or headings for a bounded record; exact revisions, observations and claim limits remain there.

- [Kernel locks](sources/kernel-locks.md)
- [Cross-layer mechanisms and observation routes](sources/cross-layer-routes.md)
- [DateRange construction](sources/date-range-construction.md)
- [Temporal values and extraction](sources/temporal-and-message-probes.md)
- [Temporal runtime folds](sources/temporal-runtime-fold-probes.md), including [minute/second and quarter calibration](sources/temporal-runtime-fold-probes.md#src-temporal-calibration-c19) and [membership/Date-validity calibration](sources/temporal-runtime-fold-probes.md#src-membership-validity-calibration-c20)
- [Temporal constants and BaseYear](sources/temporal-constant-and-base-year-probes.md)
- [Repeatable temporal computations](sources/repeatable-temporal-computation-probes.md)
- [Having filters](sources/having-filter-probes.md), including [captured predicate compositions](sources/having-filter-probes.md#src-captured-filter-compositions)
- [Groups and iteration](sources/group-and-iteration-probes.md), including [sparse filter traversal](sources/group-and-iteration-probes.md#src-sparse-filter-traversal) and [Number parallel tokens](sources/model-structure-and-declaration-probes.md#src-parallel-number-index-tokens)
- [Group lists and capacity](sources/group-list-and-capacity-probes.md)
- [Group-count topology and declared extent](sources/group-count-topology.md), including [reviewed inbound fixed-suffix coverage](sources/group-count-topology.md#src-group-fixed-suffix-coverage) and the [Enumeration literal gate](sources/group-count-topology.md#src-group-value-count-literal-domain).
- [Group-operand inbound evidence](sources/inbound-group-operand-batches.md)
- [Over-repetition](sources/over-repetition-probes.md)
- [Path resolution and literal index-key fitting](sources/path-resolution-class-probes.md), including the [reviewed one-pass and custom-bound controls](sources/path-resolution-class-probes.md#src-index-key-literal-fitting).
- [Static admission and classes](sources/static-admission-and-class-probes.md)
- [Diagnostic vocabulary and sweeps](sources/diagnostic-class-vocabulary-and-sweeps.md)
- [Model structure and declarations](sources/model-structure-and-declaration-probes.md), including [executable declaration phases](sources/model-structure-and-declaration-probes.md#src-executable-declaration-admission) (peer reconciliation at `6bc5e75337a6b2caea5b563e26d346cf53e163c8`)
- [Rule-set metadata](sources/rule-set-meta-information.md)
- [Computation placement and constants](sources/computation-placement-and-constant-probes.md), including [String/Enumeration crossings](sources/computation-placement-and-constant-probes.md#src-string-enumeration-crossings), [tolerance calibration](sources/computation-placement-and-constant-probes.md#src-tolerance-family-calibration) and [C21 independent controls](sources/computation-placement-and-constant-probes.md#src-peer-independent-controls-c21)
- [Computation scheduling and guards](sources/computation-scheduling-probes.md), including [guard-derived operand scope](sources/computation-scheduling-probes.md#src-computation-guard-operand-scope) and [nested String first-filled sources](sources/computation-scheduling-probes.md#src-nested-string-first-filled); [empty-prefix provenance](sources/computation-scheduling-probes.md#src-first-filled-empty-prefix) covers the validation follow-up
- [Evaluation and application](sources/evaluation-and-application-routes.md)
- [String and custom-domain ingestion](sources/domain-ingestion-probes.md), including restricted charset input, registered-domain identity and ordered computation membership admission
- [Custom-field ingestion and outcomes](sources/custom-field-probes.md), including inbound [reserved-report admission, core validation modes and computed-target checks](sources/custom-field-probes.md#src-custom-test-range) from a12-dmkits `c0a564ad30ab0baf41c4b4cac33e5452b39993a4`
- [Messages and pointers](sources/message-and-pointer-probes.md)
- [Message-cache population](sources/message-cache-probes.md)
- [Message-reference carriers](sources/message-reference-carrier-probes.md), including [filtered distinct counts and repeatable group presence](sources/message-reference-carrier-probes.md#src-message-reference-carriers)
- [Message-parameter rendering and keyed membership](sources/message-parameter-rendering-probes.md)
- [Inbound handbacks and historical Git stubs](sources/inbound-handbacks.md), including [2026-10-09 reconciliation and additional observations](sources/inbound-handbacks.md#inbound-2026-10-09-reconciliation)
- [Computation diagnostic assembly](sources/inbound-handbacks.md#src-computation-diagnostic-assembly): inbound a12-dmkits `6b919e0870e36b9da7f33e6735ea7821474e68a0`, retained in reviewed `c0a564ad30ab0baf41c4b4cac33e5452b39993a4`; post-execution full-pointer collisions and application availability.
- [Partial declared-slot walks (KF527)](sources/inbound-handbacks.md#inbound-2026-10-09-extensions): inbound `f641cc24f`, `PartialFillWalkRelevanceDiffTest` and `PartialProductCapacityDiffTest`; the route for fill, prefix and product relevance distinctions adopted in spec/10 §5.
- [Model-check class multiplicity (KF558)](sources/inbound-handbacks.md#src-inbound-kf558-multiplicity): inbound a12-dmkits `18dd8a23dedbdfc96bc62a6b0832c8aea4645430`, `CheckerClassMultiplicityAgreementTest`; the per-locale `RULE_HAS_NO_ERRORTEXT` is confirmed locally by three retained rows.
- [October 13 peer response](sources/inbound-handbacks.md#src-inbound-2026-10-13): reviewed a12-dmkits `8addfd0bf5e1e6f1c21d20d49c1eb0acaac85358`; dispositions of thirteen entries, the computed String maximum, per-entry sort capacity, per-value charset collapse, the row-loop key fault and the declaration member ranges.
- [Question-to-locus lookup](sources/kernel-loci.md)

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

- [Selected Boolean, Confirm and DateRange comparisons](sources/inbound-group-operand-batches.md#src-selected-typed-comparisons): static admission, comparison spelling, phase observations and first-filled prefix behavior.
- [Selected overlap streams](sources/date-range-construction.md#src-selected-overlap-streams): both-arm admission, selected scalar/list roles and reached-versus-bypassed poison.

<a id="src-json-row-normalization"></a>
- [Document JSON row normalization](sources/evaluation-and-application-routes.md#src-json-row-normalization): non-object removal, dense surviving coordinates, nested parent scope and the separate V1 placement route.

<a id="src-non-number-direct-alternatives"></a>
- [Direct Boolean, Confirm and DateRange alternative matrix](sources/computation-placement-and-constant-probes.md#src-non-number-direct-alternatives)
