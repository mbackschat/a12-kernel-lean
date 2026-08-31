# Open semantic gaps

This is the open-only work index for convergence toward complete semantic conformance with A12 Kernel 30.8.1. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns implemented, proved, and evidenced coverage. Working context selects uninterrupted work from this index. [`PLAN.md`](PLAN.md) persists a selection only for cross-session handoff.

## Query contract

Open the selected `gap-` record where one exists. Otherwise open the matching `SG<n>` entry.

```sh
rg -n '^<a id="gap-' docs/SEMANTICS-GAPS.md
rg -n '^### SG' docs/SEMANTICS-GAPS.md
rg -n '^- `state`:|^- `blocked-on`:|^- `reopen-when`:|^- `remaining`:|^- `route-state`:' docs/SEMANTICS-GAPS.md
```

A gap carries only current missing behavior, prerequisites, discriminators, consumer consequences, evidence needs, route state, and reopening triggers. Implemented detail stays behind an implementation-map link, exact source revisions stay behind a source-record link, and completed narrative is deleted.

## Hard-frontier critical path

The binding construction order is **SG1 → SG2 → SG4**. SG1 and SG2 are closed. [Immutable checked-document construction](IMPLEMENTATION-MAP.md#immutable-checked-document-construction) supplies one model-certified input, and the [repetition/iteration boundary](IMPLEMENTATION-MAP.md#9--repetition-and-iteration) supplies canonical addressed operands. SG4 must consume both with an explicit processing context rather than redefine document or address state.

## Keystone construction gaps

### SG4 — computation scheduling and state transition

- `state`: open
- `missing`: compose authored tables, dependency order, poison and clearing, repeatable targets, rich result projections, exact application, and later validation without collapsing checked definition, transient state, dependency outcomes, public results, source-relative deltas, or applied document state.
- `baseline`: [§11](IMPLEMENTATION-MAP.md#11--calculations-and-formal-checking) owns the bounded fixed and repeatable execution, result, application, and purpose-specific transition families. [`ARCHITECTURE.md`](ARCHITECTURE.md#whole-model-computation-execution-keeps-definition-activation-result-application-and-validation-separate) owns the required phase separation.
- `remaining`: Number and String nesting beyond two direct finite levels, plus wider multi-step calibration.
- `remaining`: cross-group fixed-target admission and execution is closed for all four constant families at the [declaring-group gate checkpoint](SOURCES.md#src-computation-declaring-group-gate), which also fixes the containment gate and measures that a repeatable declaring group adds no repetition. A repeatable *target* declared cross-group is now measured at runtime too: all four constant families compute once per instantiated target row from the root exactly as from the target's own group, which isolates the target-scope disjunct that a fixed target or a star operand had confounded in every earlier row ([checkpoint](sources/cross-layer-routes.md#src-cross-group-repeatable-constant-target)). What stays open is non-constant cross-group operations, generated-validation firing, and result/application correspondence. Do not extrapolate the target-scope mechanism to list, construction, repeatable, or generated-validation routes.

- `remaining`: the bare-constant carrier families are split out into [SG15](#sg15--bare-constant-target-families), which owns their per-kind admission, rendering, and target-check timing. Scheduling, dependency order, poison, clearing, and application stay here.
- `remaining`: the complementary refusal is **unimplemented** and has no known witness here. An unstarred per-row operand of a repeatable declaring group must refuse a fixed target outside it, and no checked elaborator derives iteration from an operand. Treat it as a constraint on the next family, not a to-do: a family admitting such an operand must derive iteration and apply containment in the same change. The checkpoint's `separator` and `local-reach` rows own the discriminator and the survey.
- `remaining`: the three carriers are not merged and should stay separate until a fourth consumer or a concrete need argues otherwise. Their result domains differ, which is the usual reason not to, and their target checks differ in *when* they run: String checks everything at runtime, Number splits its two grounds across authoring and runtime, and Boolean/Confirm has no target check to delegate at all. A shared carrier would have to abstract over that split rather than over a common check.
- `remaining`: admission across all of them is **one shared rule**: the target's declared *format string* gates the literal's temporal family, and the field's declared kind is measured irrelevant. Within a family the format then renders and may drop components silently. A carrier for any of these kinds reuses that gate rather than restating a kind-specific one; the open discriminator is whether the gate reads component sets or a coarser date/time split, which a `MM`-only format would separate.
- `remaining`: serial computed-source Enumeration chains beyond the exact four-computation `CurrentRepetition` Number-to-String-to-Number-to-filtered-Enumeration chain.
- `remaining`: computed-source forms beyond the exact Enumeration-to-`FieldValueAsNumber`-to-filtered-Enumeration and `CurrentRepetition` alternating-to-filtered-Enumeration chains, and filter producers beyond the existing addressed Number-result union. A third fixed sibling producer is duplicate overlay width over the already arbitrary completed-result list and is not a semantic work item.
- `remaining`: Repeatable target operations and result/application carriers outside the exact implemented baseline in [§11](IMPLEMENTATION-MAP.md#11--calculations-and-formal-checking) remain open. Select one only when it adds a behaviorally distinct target policy or runtime route rather than overlay width.
- `remaining`: V1 String-ingress source identity remains unrepresented for non-String computation targets outside Number. The typed checked-document route correctly uses typed equality; a future transport-facing carrier must retain whether the source V2 object is unconverted text instead of reconstructing identity from stored text or parsed value.
- `remaining`: addressed DateFragment Kernel calibration and copy-versus-render discrimination; wider-profile and cross-spelling calibration for addressed DateRange; wider format, zone, and source-shape calibration for addressed DateTime; extensible-enumeration String alternatives, nested temporal-expression extractors beyond the exact bound complete-DateTime sub-day shift, and world-backed component calibration for addressed Time construction; checked-source, cross-format, and wider-target-policy calibration for addressed FULL Date.
- `remaining`: materialized document topology beyond the exact normalized two-level repeatable Number `FirstFilledValue` target projection, later-rule execution beyond that route and the exact scalar-target generated-Number routes for direct expressions, one unfiltered repeatable sum, one correlated repeatable `FirstFilledValue`, one- and two-level ordinary direct-Number comparisons, and one-level direct-String-length comparison, plus transport reconstruction and pointer-dialect rendering.
- `remaining`: extend the checked multi-operation direct-field union and whole-call result projection to a behaviorally distinct family beyond the [closed direct-field baseline](IMPLEMENTATION-MAP.md#cap-checked-direct-field-formal-input).
- `remaining`: extend group containment beyond the fixed checked numeric operation and already resolved filter fields.
- `remaining`: extend selected-preliminary execution beyond the [named whole-call baseline](IMPLEMENTATION-MAP.md#cap-selected-computation-preliminary). The scalar and special-source baseline includes isolated parallel Number, indexed DateRange construction, and a generated Number table whose selected operation may consume a prepared repeatable aggregate and continue through separate-destination application plus explicit later validation.
- `remaining`: the exact addressed same-family baseline includes multi-star Number, Boolean, ordinary String, Custom, DateFragment, FULL Date, Time, DateTime, and sibling-star DateRange `FirstFilledValue`, plus direct and multi-operand Enumeration `FirstFilledValue`.
- `remaining`: the exact addressed conversion and construction baseline includes `DateFromDateTime`, `TimeFromDateTime`, DateRange endpoint-component, `Time(...)`, and DateTime sub-day and calendar-day shifts.
- `remaining`: the exact cascade baseline includes the Number-to-DateTime producer source, three-stage Enumeration source, Enumeration-to-`FieldValueAsNumber`-to-filtered-Enumeration source, fixed `CurrentRepetition` Number-to-String-to-Number producer source, and four-stage filtered-Enumeration final fallback.
- `remaining`: render operand messages.
- `remaining`: concrete reachability and Kernel scheduling correspondence for structural-failure arms that currently have only conditional internal laws. One route was found and it was a **defect**: an over-limit target row reached the indexed-parallel key lookup with no index-column entry and aborted the whole run, because the target inventory and the index column enumerated rows differently. The Kernel computes into in-capacity rows only ([over-limit target checkpoint](sources/group-and-iteration-probes.md#src-over-limit-computation-target)), so every repeatable-target carrier now shares one excluding row domain and that route is closed.
- `remaining`: the over-limit exclusion is measured on **three** carriers — a bare constant, a sibling-star `FirstFilledValue`, and a `DateFromDateTime` conversion — across one, two, and three repetition levels, and it is **level-independent**: an excess row at the outer, middle, or inner axis excludes its own subtree alike, so the decision is the whole environment rather than the target level's coordinate. The construction, shift, enumeration, and indexed-parallel carriers share the domain as a stated assumption. Two levels overflowing at once behave as either alone.
- `remaining`: **the clearing half is measured and implemented; one carrier's clear is not.** A target cell holding a stored value in an over-limit row is `cleared`, so the row leaves the value-producing domain and stays in the clearing one. Every addressed and constant repeatable-target carrier now emits its own no-value outcome at that row through `CheckedDocument.computationRowOutcomes`, which each application projection already turns into a clear. The indexed-parallel route is the exception: its index column carries no entry at an over-limit row, so the row is outside its execution domain, and whether that carrier also clears there is unmeasured. Its `inCapacityRowEnvironments` domain claims the execution boundary only.
- `remaining`: retain addressed-index clearing route attribution only when an Explain consumer requires it.
- `remaining`: certify source/destination model compatibility at the result type boundary only for a consumer that cannot supply the same-model precondition.
- `remaining`: retain a `NumericComputationRunFault.targetCheck` witness only if one appears. Every authorable candidate is now measured and refused: `SumOfProducts` and the infix `*`, `/`, and `^` all draw `MVK_INVALID_COMPARE_DEC_PLACES` into a narrower target unless suppressed, and suppression routes to `checkWithScaleWarningSuppressed` instead of this arm. The [assignment-scale reach checkpoint](SOURCES.md#src-unsuppressed-assignment-scale-reach) owns the measurement and states what would still defeat it.
- `evidence-needed`: one coherent separating batch for each selected wider composition family, preserving fresh versus stale reads, unreached versus reached poison, empty substitution, exact row identity, and retained action placement.
- `discriminator`: dependency edges order eligible target methods but do not pre-skip a dependent after failure. Invalidity propagates only through a reached read, which short-circuiting can hide.
- `consumer`: Execute, Compile, Analyze, and Explain must distinguish checked definition, transient activation, cause-blind dependency invalidity, rich family outcomes, source-relative results, application, and validation.
- `forbidden`: do not use deltas, applied state, or public result collections as the dependency overlay. Do not introduce a generic graph, state machine, cross-family trace framework, or registry.
- `entry-gate`: the bounded carriers listed in [§11](IMPLEMENTATION-MAP.md#11--calculations-and-formal-checking) satisfy the local entry gate. Reopen only one selected remaining family with a verified route.
- `completion-gate`: an executable checked scheduler is deterministic for fixed checked inputs and sound against an independently meaningful relation where one is justified. Result and application laws preserve every named public partition, and validation remains separate.
- `route-state`: discovery-required

## Semantic-family gaps

### SG5 — numeric authoring and target completion

- `state`: open
- `missing`: close remaining numeric authoring shapes, computation wrappers, repeated and group aggregates, temporal or aggregate overloads, concrete ingestion and rendering, and partial or repeatable integration through the shared owners.
- `baseline`: [§5](IMPLEMENTATION-MAP.md#5--numbers-and-decimals) owns scalar and addressed numeric execution. The bounded group capabilities start at [shared admission](IMPLEMENTATION-MAP.md#cap-shared-entity-list-group-admission).
- `remaining`: division- and power-valued operands inside addressed operand lists, deeper nested calls, nested wrapper or arithmetic leaves, aggregate operands, and literal, nested, or grouped addressed power.
- `remaining`: host wire ingestion, remaining group or addressed expression placements, third-level external correlation, and external calibration of operand shapes beyond direct Number copy.
- `discriminator`: keep authored literal scale, derived scale, warning suppression, source scope, target scope, and operator-local poison timing independent.
- `consumer`: Execute and Transform require exact tree shape, rounding stages, target policy, and unsafe-reassociation boundaries.
- `forbidden`: do not introduce a general recursive expression tree until two completed semantic users require the same representation.

<a id="gap-sg5-unstarred-repeatable-group-presence-reference"></a>
#### Unstarred repeatable group-presence reference

- `state`: open
- `missing`: select the group operand's own reference coordinate when group presence admits an unstarred repeatable group. The projection must remain fail-closed rather than inventing a concrete or wildcard coordinate.
- `baseline`: [group-operand reference projection](IMPLEMENTATION-MAP.md#cap-group-operand-reference-projection) covers nonrepeatable group presence and group carriers with a witnessed bound or reopened level.
- `evidence-needed`: one Kernel reference row for the admitted unstarred repeatable group-presence form at an unbound own level.
- `discriminator`: compare a concrete own-level coordinate with a wildcard own-level coordinate while preserving the same descendant expansion and outer bound prefix.
- `consumer`: Explain must not present an incomplete or invented `referenced` set for an admitted condition.
- `reopen-when`: a source route exposes the reference coordinates for this exact admitted form.
- `route-state`: discovery-required

<a id="gap-sg5-number-token-group-runtime"></a>
#### Number, token, and Boolean group runtime

- `state`: open
- `missing`: execute Boolean group value-count computation over wider fixed groups and groups with declarations below a deeper repeatable level.
- `missing`: execute non-value-count token group operands through computation, Number and Boolean plus non-value-list token group operands through partial validation, and all three families through legacy raw-`Document` routes.
- `missing`: make Number directional missingness per cell before admitting a group whose declarations disagree on signedness.
- `missing`: decide Enumeration or category `NumberOfValueInFields` literal admission over a starred group independently of the current all-declarations choice.
- `prerequisite`: legacy raw-`Document` readers must expose instantiated-row topology before enumerating the operand-bounded group extent.
- `baseline`: [Number group aggregates](IMPLEMENTATION-MAP.md#cap-number-group-aggregates), [token group expansion](IMPLEMENTATION-MAP.md#cap-token-group-expansion), and [Boolean/Confirm group value count](IMPLEMENTATION-MAP.md#cap-boolean-confirm-group-value-count) own the checked-document subsets.
- `evidence-needed`: measure each remaining refused route and isolate declared-tail effects from no-row and instantiated-empty prefixes before representing omitted capacity.
- `discriminator`: vary rule depth, operand depth, instantiated rows, declared capacity, and signedness independently while keeping recursive declaration expansion fixed.
- `consumer`: Execute needs exact operand-bounded extent and fillability. Analyze needs encounter order and the distinction between authored slots and reached cells.
- `reopen-when`: a coherent group-runtime batch is selected.
- `route-state`: discovery-required

#### SG5 family completion

- `completion-gate`: every legal numeric operator and authoring region is checked and executable where the Kernel permits it. Illegal shapes fail at the correct static layer, and target rendering, application, and fillability retain their separators.

<a id="gap-sg6-temporal"></a>
### SG6 — temporal authoring, calendar, and target completion

- `state`: open
- `missing`: temporal parsing, admission, construction, model-zone legacy calendar stepping, additions and differences, DateRange operations, partial and formal propagation, and stored or computed targets must preserve exact instant, decoded components, format, and calendar provenance together.
- `baseline`: [§6](IMPLEMENTATION-MAP.md#6--dates-and-time) owns implemented temporal boundaries. [Temporal comparison and aggregates](IMPLEMENTATION-MAP.md#cap-temporal-comparison-and-aggregates), [checked DateRange declaration](IMPLEMENTATION-MAP.md#cap-date-range-checked-declaration), and [checked direct DateRange bounds](IMPLEMENTATION-MAP.md#cap-checked-date-range-bound) own the principal DateRange subsets.
- `remaining`: one declared-format stored-input classifier across temporal kinds. The twelve-format by three-kind external differential is closed over its discriminating values, while Lean currently owns the DATE forms plus bounded `HH:mm:ss` Time and ISO DateTime profiles; checked-document integration for standalone classifiers, remaining zones and pre-floor identities, unmeasured stored texts, every format outside the 135-candidate declaration denominator, and the deliberately imprecise `DATE_FRAGMENT` stored-value form remain open.
- `remaining`: remaining repeatable placements, broader recursive lowering, partial validation, rule and message integration, wider operands, and stored or computed target coverage.
- `remaining`: materialized topology, later validation, valueless-source reason propagation, and maintained result/application correspondence for `DateFromDateTime`; sibling-parallel placement is statically closed as illegal for both DateTime component extractors.
- `remaining`: external per-row `ValueAsDate` execution and the other temporal carriers' reading loci.
- `remaining`: computed-target routes for component-omitting Date values and their wider repeatable placement. Aggregate admission is already owned by the shared temporal-format gate.
- `remaining`: wider semantic-index DateRange construction, keyed slots inside overlap lists, keyed operands on both sides, computation-phase keyed-column strictness, field-valued key emptiness or invalidity, and invalid cells in unselected rows.
- `remaining`: exact diagnostic projection for keyed DateRange refusal classes.
- `remaining`: the complete generated-format equivalence denominator for unconfigured `interpretationOfYear`, plus every affected consumer. The current field-local classifier remains fail-closed for this branch.
- `remaining`: unconfigured interpreted direct-list execution, other computation families under an interpretation, and configured interpreted profiles beyond the measured subset.
- `remaining`: the unconfigured yearless per-row scalar-plus-star overlap shape, filtered-star operands beside a row read, non-stored overlap reads, and wider repeatable overlap execution.
- `remaining`: DateRange fragment formal outcomes, empty and formal constructor-target branches, wider direct lists beyond three sources, and external calibration for internally composed profiles.
- `remaining`: day and year endpoint-component runtime values and validation-surface execution.
- `consolidation-candidate`: `CheckedDateRangeBoundComponent` overlaps the richer endpoint-component operand read but still exposes the selected endpoint observation needed by Explain. Consolidate only by giving the operand read that retained observation, with owner approval.
- `risk`: equal Berlin wall labels can denote different instants, and another `World` can change `Now`. Wall-label identity, early clock resolution, or elapsed-duration substitution is unsound.
- `consumer`: Execute, Transform, and Explain must retain instant, source format, decoded components, calendar profile, world dependency, and target rendering policy. Unsupported zone or profile information is explicit insufficiency.
- `forbidden`: do not create a parallel temporal AST, re-resolve an instant, invent target rendering, substitute proleptic dates for an unsupported profile, or equate calendar steps with elapsed duration.
- `evidence-needed`: select one coherent temporal family and use the matching keyed checkpoint in [`SOURCES.md`](SOURCES.md). Do not infer an unmeasured carrier from an adjacent carrier with the same value outcome.
- `entry-gate`: each selected family needs one bounded source packet and a separator matrix over format, world, profile, gap or overlap, cutover, empty or formal precedence, and target policy.
- `completion-gate`: every admitted temporal operation and target path is checked across its legal profile with exact empty and formal polarity plus separating gap, overlap, cutover, and millisecond cases.
- `route-state`: discovery-required

### SG7 — String, pattern, and custom-field completion

- `state`: open
- `missing`: general String ingestion, every String function, pattern admission and execution, Unicode and line-break policy, repeatable lists and requiredness, custom-field output, and String targets must share one checked observation without bypassing normalization or resampling validators.
- `baseline`: [§7](IMPLEMENTATION-MAP.md#7--strings-and-patterns), [§8](IMPLEMENTATION-MAP.md#8--enumerations-and-value-lists), and [String/Enumeration distinct count](IMPLEMENTATION-MAP.md#stringenumeration-distinct-count) own the implemented surface.
- `remaining`: model-owned checked message-template authoring before raw interpolation, remaining grapheme restrictions, and surrogate-splitting reachability.
- `remaining`: registered-Custom consumers and repeatable computed target families beyond the bounded exact-address `FirstFilledValue` carrier.
- `remaining`: Custom beside String in `FieldValuesNotUnique`, plus stored-text versus decoded identity calibration for temporal declarations beyond the measured default Date profile.
- `remaining`: Custom validity over Enumeration and extensible-Enumeration operands, its operand field, wildcard, and value-validation static gates, and `ValidationCondition` leaf integration.
- `remaining`: determine whether an unregistered declared Custom type is statically rejected, raised at runtime, or degraded. The current checked declaration remains a local narrowing until measured.
- `remaining`: keep the unregistered predefined-type double-firing mechanism observable-only until its accepted upstream experiment isolates the cause.
- `consumer`: Execute and Explain require normalized text, placement, validator identity, and display bytes.
- `completion-gate`: every legal String or Custom operation and target uses one normalized observation. Repeatable and partial consumers preserve exact cause and order, and unsupported host capability or syntax fails closed.
- `route-state`: discovery-required

### SG8 — Enumeration and value-list completion

- `state`: open
- `missing`: open, dynamic, and partial declarations, remaining repeatable projections, computation filters, RNU authoring, and overloaded value-list consumers must reuse the typed projection and quantifier core without erasing declaration domains.
- `baseline`: [§8](IMPLEMENTATION-MAP.md#8--enumerations-and-value-lists) and [String/Enumeration aggregate counts](IMPLEMENTATION-MAP.md#stringenumeration-aggregate-counts) own the implemented surface.
- `remaining`: dynamic enumeration ownership and partial declarations. Table-backed declarations reopen only if a table-name or dependent-column producer becomes reachable.
- `remaining`: independently calibrate token value-count partial runtime, semantic-root versus physical-root identity, and three or more nested repeatable levels.
- `remaining`: `FirstFilledValue` beyond three direct sources, including mixed, group, filtered, nested, validation, and wider temporal policy routes.
- `remaining`: computed-source Enumeration beyond the [exact one-producer filtered cascade](implementation/strings-and-enumerations.md#cap-number-dependency-in-enumeration-having), [two-producer ordered join](implementation/strings-and-enumerations.md#cap-two-producer-enumeration-firstfilledvalue-join), and [computed Enumeration value plus Number filter join](implementation/strings-and-enumerations.md#cap-computed-enumeration-number-having-join) is owned jointly with SG4, including wider producer and source shapes.
- `prerequisite`: reuse addressed operands, kept-successor traversal, repeatable expansion, and checked RNU topology. Audit dynamic domain ownership before widening.
- `consumer`: Execute and Transform require positional categories, union admission, many-to-one identity, and directional empty or unknown behavior.
- `completion-gate`: every legal declaration profile, projection, domain rule, repeated access, value-list operation, and uniqueness use is checked with display, domain, and category distinctions preserved.
- `route-state`: discovery-required

### SG9 — paths, indices, and static legality completion

- `state`: open
- `missing`: bilingual parser and renderer paths, lexical and dot syntax, semantic indices, globals, nested or multiple stars, wider RNU `@From`, and remaining diagnostics must resolve through one checked namespace.
- `baseline`: [§10](IMPLEMENTATION-MAP.md#10--paths-and-references) owns implemented paths. The [cross-clause diagnostic owner](IMPLEMENTATION-MAP.md#cross-clause-implementation-notes) owns exact projections and explicit unmapped refusals.
- `remaining`: nested or different repeatable scopes, parallel RNU mapping, other group-list or count shapes and arities, parser-level `SumOfProducts` star and `Having` refusals with exact diagnostic projection, other assembly refusals, and executable newly admitted conditions.
- `remaining`: fixed nonrepeatable descendants and wider comparison, computation, partial-validation, arithmetic-wrapper, and parser forms of `CurrentRepetition`.
- `remaining`: computation has no semantic-index source that can represent direct reads of a computed field or naming it as an index key.
- `remaining`: an empty **nonrepeatable** group is kernel-valid ([checkpoint](SOURCES.md#src-empty-declared-group)) and `FlatModel` cannot express one, because it represents a group only through its fields or its own repeatable declaration. The message group position's root gate is the one that would diverge if the input could be built, reporting its undeclared-root class where the Kernel reports the ordinary group class. Lifting it means giving groups their own declaration list, a core-type change needing owner approval, so no local work proceeds on that route. Select it only when a named consumer needs an empty group represented; an importer or refactoring round-trip is the likeliest first.
- `remaining`: multi-root addressing is measured only for the bare-name tiers ([checkpoint](SOURCES.md#src-multi-root-short-name-reach)). Unmeasured across roots: the short-name flag disabled, a repeatable group in a second root, a name duplicated within one root while unique in another, and whether any other model-wide index shares that reach.
- `evidence-needed`: measure a semantic-index projection inside `Having` only after a filtered Enumeration source can express a live no-self-read control.
- `discriminator`: bare name, parent walk, and named turning point can spell neighboring routes. Equal local indices under different outer rows remain distinct, and unavailable index columns have phase-specific effects.
- `consumer`: Translate, Transform, and Explain require stable declaration and row identity, preserved authored-path distinctions, and exact static failure classes.
- `forbidden`: do not use string-splitting semantics, invented quoting or case rules, first ambiguous match, flattened row identity, or UNKNOWN for structural failure.
- `entry-gate`: complete one bounded source packet and separator matrix for the selected path or index family.
- `completion-gate`: every legal reference resolves deterministically, every illegal form receives the correct static class, and rendering round-trips for the supported surface.
- `route-state`: discovery-required

### SG10 — message construction and formal-output integration

- `state`: open
- `missing`: authored template parsing, token legality, path, star, index, category and `BaseYear` lookup, locale and display providers, format errors, custom output, repeatable pointers, and validation or computation orchestration must produce exact structured messages without changing firing.
- `baseline`: [§13](IMPLEMENTATION-MAP.md#13--message-interpolation) and [§12](IMPLEMENTATION-MAP.md#12--validation-and-polarity) own the implemented rendering, pointer, attachment, and structural-reference subsets.
- `remaining`: the `$#…$` group position carries its measured **static admission**, both resolution gates, and the quoting rule ([§13](IMPLEMENTATION-MAP.md#13--message-interpolation)). What stays open in it: what an admitted group parameter renders, which needs a runtime observation rather than a static one; the character **position** the Kernel's lexer class carries, which this fragment does not track; and whether a quoted segment may carry characters a bare one may not. The three lexical **classes** are closed — this entry had recorded the missing position as the reason the classes were collapsed, and that reason was wrong: the class follows the malformed shape and only the position needs a character offset.
- `remaining`: still unmeasured in that bundle are the group index and the semantic-index suffix in the name position, what any admitted group parameter *renders*, whether the retired-terminal set is selected by condition language at all, the German condition language, and every non-rule parameter owner sharing the terminal bundle.
- `remaining`: locale and display invocation, label providers, category, index and `BaseYear` lookup, custom output, repeated pointers, `NumericTargetError` codes, and rendering orchestration.
- `remaining`: complete field-owned requiredness grammar, German tokens, provider invocation, empty-value fallback, other typed producers, computation targets, and registered Custom validators.
- `remaining`: filtered-star reference operands in Number, token, and Boolean or Confirm families need a coordinate witness or a firing-scope audit.
- `remaining`: `RepetitionNotUnique` structural references and cross-repetition coordinates remain refused.
- `remaining`: add a reference field to `FlatRuleMessage` only for a shipment consumer that receives messages without their checked rule.
- `remaining`: widen `MessagePointer` for nonrepeatable context coordinates and `fillToFix` only for a named consumer of the corresponding Kernel accessors.
- `remaining`: the computed target's self-validation message has its **field** inventory and its `fillToFix` projection ([capability](IMPLEMENTATION-MAP.md#cap-computation-self-validation-type)). What that leaves to this gap is the pointers' repetition coordinates: one measured message carries a repetition-free address bare and a repeatable-crossing one fully coordinated with the starred axis at the wildcard, and the starred axis carries an unbound value measured off the Kernel pointer's own repetition indexes and invariant in the row count, so the domain question is answered and only representing it here remains.
- `remaining`: represent the keyed no-match error address as no matching row rather than as a wildcard or physical row.
- `remaining`: keyed message-parameter admission needs a condition spine carrying keyed leaves. Rendering and a key field absent from the condition remain unmeasured.
- `remaining`: the over-repetition finding **set** is measured — one `zuGrosseZeile` on the outermost violated row plus one `zuGrosseKontextnummer` per instantiated descendant row and present cell the document writes beneath it, every message naming that outermost group ([multiplicity](sources/over-repetition-probes.md#src-over-limit-finding-multiplicity), [attribution](sources/over-repetition-probes.md#src-nested-over-limit-attribution)). Representing it must carry the absorption, because a nested over-limit row is unreportable while its ancestor stands and the Explain consumer's violated-group set is therefore not the document's. The absorption is transitive to any depth and carries the ordinary-check suppression with it, so a malformed cell anywhere in the violated subtree is silent while the same value in an in-capacity sibling row reports ([absorption depth](sources/over-repetition-probes.md#src-over-limit-absorption-depth)).
- `remaining`: the address **spelling** stays open beside that set. The reviewed overload matrix carries a repetition-one index and none on the row-level code, while the runtime probe elides repetition-one throughout and indexes the over-limit row; the elision is measured on three levels at once in the attribution checkpoint. Whether that is a rendering dialect or a channel difference needs one fixture observed through both routes.
- `consumer`: Explain and Govern require structured provenance, pointers, exact bytes, severity, and polarity. Missing providers or pointer shapes are explicit insufficiency.
- `forbidden`: do not repeatedly replace or reparse inserted bytes, invent fallback, add a second lookup path, attach before verdict, or let formatting affect semantics.
- `entry-gate`: complete one source packet and separator matrix for the selected message family.
- `completion-gate`: legal routes render with exact order, locale, pointer, severity, and polarity. Invalid templates fail at authoring, and messages have no semantic back-effect.
- `route-state`: discovery-required

### SG11 — custom-condition checked orchestration

- `state`: open
- `missing`: registration, static restrictions, effective data, relevance, formal and pointer construction, host call order, messages, and whole-rule integration must surround the pure reached-leaf oracle without unsupported locality or monotonicity laws.
- `baseline`: [§14](IMPLEMENTATION-MAP.md#14--custom-conditions) owns the pure successful callback leaf.
- `remaining`: retain the exact `nameOhnePunkt` grammar and construct the shared message pointer around the reached callback.
- `prerequisite`: checked document supplies data and SG10 supplies formal output. Host failures remain explicit integration outcomes unless Kernel behavior establishes otherwise.
- `consumer`: Execute and Qualify require a concrete host contract and observable call discipline.
- `completion-gate`: checked authoring and orchestration reproduce registration, eligibility, projection, order, failure, and message behavior while retaining current non-laws.
- `route-state`: discovery-required

### SG13 — group-list and group-count completion

- `state`: open
- `missing`: every group-list predicate and filled-group count must reuse the resolved group product or structural terminal-row count while preserving partial relevance, wildcard expansion, filter order, computation poison, and decisiveness.
- `baseline`: [resolved validation group presence](IMPLEMENTATION-MAP.md#resolved-validation-group-presence), [checked group-star terminals](IMPLEMENTATION-MAP.md#checked-group-star-terminals), and the SG5 group capability records own the implemented subsets.
- `remaining`: structural and call-local group errors, repeatable operands, and value-reading computation behavior beyond the measured fixed direct-field shape.
- `remaining`: **repetition depth is measured and the refusal is lifted.** A descendant two repetition levels below the operand counts exactly as one level does, at the [deep checkpoint](sources/group-and-iteration-probes.md#src-deep-repeatable-descendant-group-count), so `repeatableDescendantShape?` no longer gates on the axis count and the clause is stated for any depth — the mechanism is subtree containment, which the validation arm already used unbounded. The **half-instantiated** shape is measured too: the outer row alone is content, on both spellings of that document, so the constituent is any row in the subtree rather than a row at the deepest level. Outbound as [`SPEC-2026-08-30-08`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-30-08) and [`SPEC-2026-08-30-09`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-30-09). Still open on the shape: three or more repetition levels, and an over-limit row at the inner level.
- `remaining`: the fixed operand's row-domain discriminator is **closed as unreachable**, not pending. Its clause counts any instantiated row where the starred count excludes over-limit ones, and separating them needs a row set whose every index exceeds capacity. No such document exists: rows are a dense array from index 1, a nonrepeatable group is `repeatability: 1` so a repeatable one is at least 2, and `repeatability: 0` is refused by the Kernel. The [row-domain checkpoint](sources/group-and-iteration-probes.md#src-group-count-row-domains) carries the three contracts. `RowAddr.path` is simply more permissive than the document format.
- `remaining`: a starred group owning its own repeatable descendant is **calibrated**, at the [row-domain checkpoint](sources/group-and-iteration-probes.md#src-group-count-row-domains): it counts its own rows undisturbed by the level below, and its in-capacity domain holds on that carrier rather than being inherited from the flat one.
- `remaining`: the ancestor-beside-descendant-star pair is **closed by refutation**. This project answered it at runtime — counting twice, with no overlap gate and no deduplication — and the Kernel never reaches runtime, refusing the pair `MVK_DUPLICATE_PARAM2` at authoring time in either order, on a pure shell exactly as on a group owning a field ([static-gate checkpoint](sources/group-and-iteration-probes.md#src-group-count-static-gates-both-arms)). The two conformance cases locking the counting answer were deleted rather than corrected, because the shape they counted is unauthorable. A duplicate starred group adding once per authored position is measured and holds.
- `remaining`: a **nested star** — the wildcard on the inner level of a two-level repeatable chain — refuses `missingBinding` for the enclosing level. That is a property of the unbound outer environment supplied, not a representational refusal, so the shape stays unclassified until it is read in a context that binds the outer level. A filtered star and a starred path navigating by parent count are untested here and keep their prior status.
- `remaining`: lists above the measured fixed arity, partial fixed or starred multi-entity lists, filtered group operands, relevance timing, and poison or lookahead policy.
- `remaining`: the mixed validation group-count list is **implemented and Kernel-calibrated**; [`cross-clause.md`](implementation/cross-clause.md#cap-mixed-validation-filled-group-count) owns its coverage. The all-fixed list keeps the operand-list extent, which is measured and correct, and the two carriers must not be merged onto one quantity.
- `remaining`: the **computation arm's static gate table is measured and matched**. Every class and the containment-before-rootness order reproduce there exactly as in rules, so both arms now call one containment predicate and one root gate; the computation arm had gated overlap over its fixed operands only and carried no root gate at all. Still open on that arm: the same table under a repeatable declaring group and a filtered star.
- `remaining`: two of that carrier's open items are **measured and closed** at the [unavailability checkpoint](sources/group-and-iteration-probes.md#src-group-count-unavailability). An unavailable member's interaction with the sum: a fixed member makes the count unknown only where its own presence is undecided, and a starred member contributes no unknown of its own even when a row's only non-empty cell is malformed. A starred member owning a further repeatable descendant: its rows are **not** multiplied by that descendant, which is the opposite of `NumberOfFilledFields` and the reason the two extents must stay apart.
- `remaining`: an unretained repeatability is **closed as unreachable** rather than pending. A group declaring no maximum is nonrepeatable rather than unbounded, so no authorable model reaches the `none` branch several clauses keep as a total function ([declaration-domain checkpoint](sources/group-and-iteration-probes.md#src-repeatability-declaration-domain)). Two starred members and the duplicate gate are measured and implemented; the gate is **containment**, not distinctness, since two stars naming the same group are admitted and double-count.
- `remaining`: the scalar `GroupNotFilled` is the one reader of the group state still deriving its own unknown condition from the raw `erroneous` flag. It answers `.unknown` on a group holding admitted content beside an error, where the same state is `.filled` for `GroupFilled`, for the tally quantifiers, and now for the count; under the measured rule it should be `.notFired`.
- `remaining`: that leg is **not escalated and not changed**, because it is unobservable through the accepted route. The DSL has no negation, a rule emits a message only when its top-level verdict fires, and `.unknown` and `.notFired` both stay silent and combine identically under strong-Kleene conjunction and disjunction. No document distinguishes the accounts, so the shape is not ready as an `EXP-`. It is recorded because an Explain consumer reading the leaf verdict does see the difference, and because the uncited case locking it is the [`LF118`](LEAN-FINDINGS.md#lf118--an-expected-value-derived-from-the-implementation-is-not-a-lock-and-native_decide-makes-it-look-like-one) tell.
- `remaining`: the coverage leg of that rule is **unmeasurable on the accepted route, established rather than assumed**: the `:adapter:kernelProbe` request schema admits exactly `validateFull` and `compute`, and a12-dmkits' `KernelAdapter` exposes `validateFull` as its only validation entry point. Reaching `validatePart` needs a new adapter capability, not a probe request. Recorded so a later session does not re-derive the limit; [`SPEC-2026-08-31-05`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-05) carries it outbound.
- `remaining`: the count's **unavailability rule was corrected against the Kernel** at that checkpoint and is outbound as [`SPEC-2026-08-31-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-01). A formal error blocks only the negative answer, so the shared clause now reads each operand through the decided-presence projection its own group-list predicates use. The structural over-limit error on a group with admitted content is measured at that checkpoint's own `structural-error` row and behaves as the rule predicts, so the rule is about undecided presence rather than one error channel. Still open on that dimension: a call-local partial-coverage error and `noneRelevant` coverage — both follow the shared mechanism rather than a row, because `validateFull` cannot observe partial coverage.
- `remaining`: partial addressed evaluation of the mixed count is structurally unsupported rather than answered, and no measurement covers it. The comparison shape is a count against a literal threshold; a mixed count inside wider arithmetic is untested.
- `remaining`: the implicit self-validation message's type is closed for a starred operand and its direction; what the [message-polarity checkpoint](sources/group-and-iteration-probes.md#src-starred-operand-message-polarity) leaves open at its own `limit` is a nested or filtered star, a non-Number target, a starred operand inside a precondition, and whether a declared minimum interacts. The over-limit row's effect on the type is **measured**, from the group-count capture's own retained rows rather than a new one.
- `remaining`: the fixed operand's movement over a repeatable descendant is **measured and the clause is corrected**. The extent is the subtree's declared *slot capacity*, not its declared field count, at the [nested-capacity checkpoint](sources/group-and-iteration-probes.md#src-filled-field-count-nested-capacity); the two quantities coincide on every flat subtree, which is why the wrong one shipped. The prediction was reproduced on a second model built only to test it. Still open at that checkpoint's own `limit`: two nesting levels, an operand group under a repeatable ancestor, and whether `NumberOfFilledGroups` over a *list* of group operands carries the same coincidence — its extent is the operand-list length, a quantity that measurement does not reach.
- `discriminator`: nonrelevant content or a later failed expansion beside an earlier decisive group separates eager, leaking, and correct prefix accounts.
- `consumer`: Execute and Explain require exact product or count, relevance, environment, and reached failure. Analyze requires operand order and decisive prefix.
- `forbidden`: do not use caller-supplied relevance on a full document, share validation and computation scans accidentally, infer rows from patterns, or use UNKNOWN or poison for structural failure.
- `entry-gate`: select one result-domain family and show that existing product, tally, and traversal owners express every observed branch.
- `completion-gate`: every admitted direct, list, starred, partial, filtered, and count consumer delegates to the established owner with exact order, relevance, error, polarity, and poison behavior.
- `route-state`: discovery-required

<a id="sg15--bare-constant-target-families"></a>
### SG15 — bare-constant target families

- `state`: open
- `missing`: one bare authored constant per declared kind reaching a repeatable target, with that kind's admission rule, its stored rendering, and its target-check timing each measured rather than carried across a kind boundary.
- `baseline`: [`repeatable-computations.md`](IMPLEMENTATION-MAP.md#11--calculations-and-formal-checking) owns the landed carriers; [SG4](#sg4--computation-scheduling-and-state-transition) keeps scheduling, poison, clearing, and application.
- `remaining`: **four target-check timings are now measured and they do not reduce to one.** String checks everything at runtime; Number splits its two grounds across authoring and runtime; Date and Time check at neither, the declared format being a rendering; ENUM checks the constant's *value* statically. No kind's timing may be read across the boundary — Number already falsified reading String's, and Date produced a timing neither has.
- `remaining`: the repeatable **constant** carrier now has three consumers, Boolean/Confirm, ordinary String, and ordinary Number. Result and application correspondence is external evidence pending for all three, as is the applied document state after a target rejects a constant and whether a stored prior value survives that rejection.
- `remaining`: **DATE is measured and implemented**, and [`cap-repeatable-date-constant-computation`](implementation/repeatable-computations.md#cap-repeatable-date-constant-computation) owns its coverage. Its target-check timing is a *third* one: no check at either time. The static gate reads only the literal's spelling — a calendar-valid, zero-padded `DD.MM.YYYY` in double quotes — and the runtime renders that one value into whatever format the target declares, silently discarding components for a target such as `yyyy` ([checkpoint](sources/cross-layer-routes.md#src-date-constant-target-formatting), outbound [`SPEC-2026-08-31-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-02)). The carrier reuses `FullDateTargetFormat`, whose renderer already produces the two measured complete-format strings.
- `remaining`: the component-omitting Date target is a stated exclusion of that carrier rather than a Kernel refusal — `ofSource?` does not admit it and no full-Date renderer here drops components, so the carrier declines while claiming no Kernel class. Still open for the family: the pre-1900 target, a seeded target cell, and a constant under a precondition.
- `remaining`: the remaining kinds are **audited as a batch and no longer need one kernel round each** ([checkpoint](sources/cross-layer-routes.md#src-constant-literal-family-gate), outbound [`SPEC-2026-08-31-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-03)). **TIME is implemented** ([`cap-repeatable-time-constant-computation`](implementation/repeatable-computations.md#cap-repeatable-time-constant-computation)); ENUM and DATE_FRAGMENT admit a bare constant and remain to write; DATETIME and DATERANGE have no known witness at that revision and stay unrepresentable for want of one, not by decision.
- `remaining`: the Time carrier is **strictly narrower than the Kernel on one measured cell** and says so: a DATE-declared field whose format is `HH:mm:ss` admits the clock constant and stores it, while the shared `CheckedTimeTarget` also requires `kind = .time` and declines. Widening that certificate would change every family built on it, none of which has a cross-kind measurement, so the exclusion is deliberate and claims no Kernel class. Closing it properly means measuring the cross-kind cell for the *computed* Time and Date families first.
- `remaining`: **ENUM is the exception worth its own carrier decision.** Its target constrains the constant's *value* statically — an undeclared literal is refused `MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON` — which is a fourth target-check timing and the only one so far that a carrier must enforce at elaboration rather than delegate to a renderer.
- `remaining`: **ENUM was already implemented** and the audit found it so — [`cap-enumeration-result-and-application`](implementation/strings-and-enumerations.md#cap-enumeration-result-and-application) owns it, membership gate included. The rows added only its refusal's Kernel identity.
- `remaining`: **DATE_FRAGMENT is closed by the Date carrier rather than by a carrier of its own.** The Kernel decides this shape from the declared format string alone, so a `yyyy-MM` DATE and a `yyyy-MM` DATE_FRAGMENT take the same constant and store the same text; the [Date carrier](implementation/repeatable-computations.md#cap-repeatable-date-constant-computation) now admits all three year-leading component-omitting formats and needs no second owner.
- `remaining`: `OmittedComponentDateFormat` was added as a **separate type** from `FullDateTargetFormat` rather than widening it. The latter carries `parseComponents?`, which reads a stored cell back into a date, so widening would have forced an unmeasured answer to how a stored `2024` parses. Reading such a target back is the open question there, and it is a genuinely different one from rendering into it.
- `remaining`: the component-dropping renderer now covers all four measured formats — `yyyy`, `yyyy-MM`, `yyyyMM`, `MM`, and `MM-dd` — with the yearless two gated on a declared Base Year and storing no year regardless ([Base Year store checkpoint](sources/cross-layer-routes.md#src-base-year-yearless-store)). What stays open is the compact `MMdd` and `ddMM` spellings. Their declarability is already measured by [`cap-omitting-date-input`](IMPLEMENTATION-MAP.md#cap-omitting-date-input), which classifies all seven on the stored-input side; the missing observation is what a constant *stores* into them, and their order cannot be inherited from the dashed siblings because the compact pair differs from each other in exactly that.

- `remaining`: **no DATETIME or DATERANGE literal witness is known**, here at the revision the [family-gate checkpoint](sources/cross-layer-routes.md#src-constant-literal-family-gate) records and at a12-dmkits at the revision [`SPEC-2026-08-31-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-03) names, whose typed surface offers no bare-literal spelling for either kind and builds both from constant parts instead. They stay unwritten for want of a witness rather than by decision. An earlier reading of the refused range row as evidence that *something* classified there is withdrawn: `MVK_INVALID_COMPARE_TO_DATE_RANGE` is the declared-component-set mismatch, which this project's own [DateRange fragment control](sources/date-range-construction.md#src-date-range-fragment-first-filled) draws with no literal anywhere in the condition.
- `remaining`: open across the whole family: the applied document state after a target rejects a constant and whether a stored prior value survives, a constant under a precondition, and a seeded target cell. The compute observation reports the attempt rather than the resulting document, so this needs a route that exposes applied state.

### SG14 — mandatory-information derivation

- `state`: open
- `missing`: derived mandatory-information comparison must keep an authored numeric literal distinct from the derivation's own sentinel, so a legal literal equal to that sentinel cannot read as an absent bound.
- `scope`: only mandatory-information callers remain in scope. Parser callers are already covered by the canonical numeric narrowing clause, and the sentinel is observationally inert at their two gates.
- `baseline`: no Lean owner or spec clause represents the mandatory-information derivation.
- `remaining`: **the derivation is exposed, and the entry-gate question is answered.** The facade offers `getMandatoryInformationFromRules` over a rule collection, returning three field-name sets, verified in kernel `30.8.1` source rather than surveyed. What follows from that is a routing fact, not an observability one: it is a **model-and-rule-level** query with no document, so neither `validateFull` nor `compute` can expose it and the accepted runtime-probe route cannot reach it. a12-dmkits has no code touching the interface and lists the signature as unverified in its own survey.
- `remaining`: the observation is requested as [`EXP-2026-08-30-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#exp-2026-08-30-01), which carries the input, both accounts, their predictions, the unsatisfiable control, and the negative result. Write no Lean and no clause before it returns.
- `blocked-on`: **an owner decision, not an observation.** Reaching the query means giving a12-dmkits' adapter a typed mandatory-information capability, since it admits no kernel type across its boundary — a feature with an API surface, not a probe. The entry's `narrowed surface` record also shrinks the payoff to one arm of one visitor, so the decision is whether that arm is worth the capability. a12-dmkits has independently put the same capability to its own owner on its own merits, as an upgrade to a surveyed-but-unused kernel surface; if it lands, the measurement arrives unprompted and this entry closes without a request from here.
- `evidence-needed`: compare a sentinel-valued authored literal with an absent bound at each mandatory-information caller on both Kernel strategies. A negative result closes this entry as unobservable.
- `discriminator`: the parser caller is not a valid discriminator because both readings admit there. Only a mandatory-information caller can separate them.
- `consumer`: Analyze and Explain need no bound separated from a bound whose value equals the sentinel. Execute needs the distinction only if the derived answer reaches firing.
- `forbidden`: do not encode the sentinel as absence, state a firing consequence before observation, or model the derivation from caller source reading alone.
- `entry-gate`: establish one observable mandatory-information output before writing Lean. The output exists and is named above; what is still missing is a route that reads it.
- `completion-gate`: the derived comparison retains authored literal identity at every caller, and absence is representable only as absence.
- `blocked-on`: none
- `route-state`: discovery-required

## Cross-family conformance gap

### SG12 — retained Kernel correspondence coverage

- `state`: open
- `missing`: every implemented family ultimately needs versioned retained observations that distinguish realistic wrong accounts. Source reading, internal proofs, and peer agreement are not Kernel calibration.
- `baseline`: [`EVIDENCE.md`](EVIDENCE.md) and the [external-evidence gate](IMPLEMENTATION-MAP.md#current-external-evidence-gate) own the exact retained inventory and limits.
- `prerequisite`: use the compact semantic-evidence pipeline and an existing source-maintained a12-dmkits route when it emits the needed observation shape.
- `remaining`: for each coherent internally closed family, determine whether the current upstream route is sufficient. Otherwise request only the smallest missing producer capability.
- `determined 2026-08-30, computed-target message family`: the route is **sufficient and no producer capability is needed**. Everything still open there — a nested or filtered star, a non-Number target, a starred operand inside a precondition, a declared minimum, and the repeatable-descendant shell operand's polarity — is a message-type question over a model and its documents, which is exactly the `validateFull`/`compute` shape `:adapter:kernelProbe` already carries. What stays open per shape is **authoring**, not observation: whether `dmtool`'s structured verbs can express that model. Check that when the batch is authored rather than assuming it now.
- `determined 2026-08-30, group-count family`: same answer and the same reason. A formally invalid row, a starred group owning a repeatable descendant, a deeper repeatable descendant, and an all-over-limit row set are all model-plus-document runtime questions.
- `determined 2026-08-30, contrast`: [SG14](#sg14--mandatory-information-derivation) is the family where the route is **not** sufficient, and the difference is instructive — its query takes rules rather than a document, so no amount of `validateFull`/`compute` reaches it and the missing piece is a typed adapter capability. Route sufficiency turns on whether the question is asked of a document at all, not on how exotic the shape is.
- `discriminator`: a happy path compatible with both the chosen and a realistic wrong account does not calibrate the seam.
- `consumer`: Qualify and Govern require Kernel version, producer revision, digest, typed replay, separator, and a finite claim limit.
- `forbidden`: no source, peer, or proof as evidence, no universal claim from finite cases, no resurrected universal capture estate, no per-capsule harness, and no copied sibling patch.
- `entry-gate`: select one coherent family at a capability milestone and define its wrong-account matrix and exact retained claim.
- `completion-gate`: every correspondence claim cites retained observations with provenance, separators, replay, and explicit finite limits. Mismatches correct the theory or open a divergence.
- `route-state`: discovery-required
