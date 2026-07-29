# Open semantic gaps

This is the open-only work index for convergence toward complete semantic conformance with A12 Kernel 30.8.1. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) is the sole detailed owner of implemented/proved/evidenced coverage; [`PLAN.md`](PLAN.md) selects the immediate unit from this index.

## Query contract

<a id="lifecycle"></a>

Open only the selected `SG<n>` entry. Detailed implemented facts stay behind its implementation-map links. Search headings with `rg -n '^### (SG|SQ)' docs/SEMANTICS-GAPS.md` and readiness fields with `rg -n '^- (Open|Prerequisite|Unresolved source fact|Most dangerous discriminator|Consumer hypothesis|Forbidden shortcut|Evidence status|Entry gate|Completion gate):' docs/SEMANTICS-GAPS.md`.

A gap remains only while a Kernel behavior, static-legality rule, checked construction, or conformance obligation is open. Delete a completed entry; Git records its history. Never append a completed implementation narrative. `SG<n>` identifiers are not reused.

## Hard-frontier critical path

The binding construction order is **SG1 → SG2 → SG4**. SG1 and SG2 are closed: [immutable checked-document construction](IMPLEMENTATION-MAP.md#immutable-checked-document-construction) supplies one model-certified input, and the [repetition/iteration boundary](IMPLEMENTATION-MAP.md#9--repetition-and-iteration) supplies canonical addressed operands. SG4 must consume both with an explicit processing context rather than redefine document or address state.

## Keystone construction gaps

### SG4 — computation scheduling and state transition

- Missing invariant: authored computation tables, dependency order, poison/clearing, repeatable targets, rich result projections, exact application, and later validation must compose without collapsing definition, transient state, dependency outcomes, public results, source-relative deltas, or applied document state.
- Current boundary: [§11](IMPLEMENTATION-MAP.md#11--calculations-and-formal-checking) owns the implemented surface; the stable phase separation is in [`ARCHITECTURE.md`](ARCHITECTURE.md#whole-model-computation-execution-keeps-definition-activation-result-application-and-validation-separate).
- Open:
  - prove a named repeatable-table self-reference exclusion after the validated-model scope/path injectivity bridge exists;
  - prove universal finite-fold address ownership after the table owner exposes a compact emitted-target theorem;
  - retain route attribution for addressed index clearing when an Explain consumer requires it;
  - separate target-labelled structural faults with a reachable retained case before claiming the target label as evidenced;
  - admit same-target multiplicity only after [`SPEC-2026-07-26-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-26-03--same-target-computations-flatten-into-one-first-selected-table);
  - add heterogeneous activation/results and cross-family schedules without erasing family outcomes or processing-context requirements;
  - source missing-ancestor creation, destination compatibility, whole-document application, and later validation as separate phases;
  - calibrate multi-step String/Number composition and repeatable computation against separating retained Kernel observations.
- Unresolved source fact: the capability packet closes supplied order/cycle rejection, flattened first selection, reached-read poison, stripping/overlay, eager operand checking, pointer result partition, application order, validation timing, and locus-dependent repeatable clearing. Reopen only for same-target multiplicity, a new target family or processing context, missing ancestors, rendering, destination compatibility, or another uncovered engine-layer composition.
- Most dangerous discriminator: dependency edges order generated target methods but do not pre-skip a dependent after failure. Invalidity propagates only through a reached read, which short-circuiting can hide. Parallel index clearing is a separate coarse, locus-dependent mechanism.
- Consumer hypothesis: Execute, Compile, Analyze, and Explain must distinguish checked definition, transient activation, cause-blind dependency invalidity, rich family outcomes, source-relative results, application, and validation. Private schedule/list order is not a public collection-order contract.
- Forbidden shortcut: do not use deltas, applied state, or public result collections as the dependency overlay; merge eager operand errors with dependency poison; duplicate the checked document/address plan; or introduce a generic graph, state-machine, trace, or registry.
- Evidence status: maintained a12-dmkits differentials Kernel-lock isolated repeatable/index and value-less-target result-channel seams. Multi-step composition, finite repeatable plans, heterogeneous results, destination compatibility, and whole-document transition remain partially or wholly `external evidence pending`.
- Entry gate: passed for String, scalar Number, and the conservative repeatable Number packet. Reopen only at the source triggers above.
- Completion gate: an executable checked scheduler is deterministic for fixed checked inputs and sound against an independently meaningful relation where one is justified; result and application laws preserve every named public partition and validation remains separate.

## Semantic-family gaps

### SG5 — numeric authoring and target completion

- Missing invariant: close the remaining numeric authoring shapes, computation power/wrappers, repeated/group aggregates, temporal/aggregate overloads, concrete ingestion/rendering, and partial/repeatable integration through the shared owners.
- Current boundary: [§5](IMPLEMENTATION-MAP.md#5--numbers-and-decimals), [resolved Number aggregates](IMPLEMENTATION-MAP.md#resolved-number-aggregates), [String/Enumeration aggregate counts](IMPLEMENTATION-MAP.md#stringenumeration-aggregate-counts), and [resolved group presence](IMPLEMENTATION-MAP.md#resolved-validation-group-presence) own the implemented surface.
- Open: Boolean/Confirm value-count integration must use the fixed canonical lowercase tokens and must not acquire model token metadata from the ignored `@NotInD` declarations. Concrete Boolean/Confirm ingestion and Number formal-read checking remain unimplemented; the latter must preserve the stored value regime so decimal-valued input receives the strip-and-minimum-scale projection while String-valued input remains verbatim, without replacing exact decimal source identity. Remaining group/addressed expression placements must reuse their existing family owners.
- Completion gate: every legal numeric operator and authoring region is checked and executable where the Kernel permits it; illegal shapes fail at the correct static layer, and target rendering/application and fillability retain their separators.
- Consumer and evidence: Execute and Transform require exact tree shape, rounding stages, target policy, and unsafe-reassociation boundaries. Project-local portable calibration remains partial.

### SG6 — temporal authoring, calendar, and target completion

- Missing invariant: temporal parsing/admission, construction, model-zone legacy calendar stepping, additions/differences, DateRange operations, partial/formal propagation, and stored/computed targets must preserve exact instant, decoded component, format, and calendar provenance together.
- Current boundary: [§6](IMPLEMENTATION-MAP.md#6--dates-and-time) owns the implemented temporal surface. Signed Berlin constructed-Date shifts are internally closed after the checked floor with source-offset day landings, sign-independent month/year compute-time landings, exact milliseconds, and operation-specific calendar corrections. Checked two-step constructed-Date and DateTime continuations consume the inner result's exact instant directly and preserve repeated-midnight identity. Direct field-backed and dynamic-`Now` DateTime `AddDays` are closed under UTC/GMT and Berlin with exact source instant, wall clock, milliseconds, numeric omission provenance, generated source-before-amount order, and explicit per-call world transport; the field-backed result feeds direct-DateTime `DifferenceInDays` in either authored position and also flows through a distinct declaration-owned DateTime target, rich result view, source-relative change/clear classification, and exact application. Field-backed and dynamic-`Now` `AddHours`/`AddMinutes`/`AddSeconds` expose the whole shifted DateTime with exact instant, model-zone label, milliseconds, omission, and cause order; `TimeFromDateTime` is proved to be only their wall-clock projection, while each whole result reaches the checked DateTime target/result/application path. Either exact sub-day source also feeds one further cross-unit sub-day shift with exact inner-before-outer evaluation and accumulated omission. Either exact sub-day source feeds one calendar `AddDays`, preserving elapsed-then-calendar order, the inner source offset through Berlin gap/overlap landings, exact milliseconds, omission, cause order, and explicit per-call world transport. One field-backed calendar `AddDays` result also feeds one sub-day shift; the reverse order remains distinct at the spring gap and at equal autumn overlap labels with different exact instants. Either exact sub-day source feeds `DifferenceInHours`/`DifferenceInMinutes`/`DifferenceInSeconds` with one direct DateTime in either authored position without rendering or re-resolution; repeated-hour identity, per-call world transport, and millisecond truncation remain observable. DateTime month/year shifts remain statically unrepresentable. Checked constructed-Date differences retain all three units under UTC/GMT and Berlin, with exact-instant ordering, source-relative month/year qualification, authored sign, and reason-bearing non-values; the bounded mixed shift/direct form works in either authored position and retains a value-carrying shift's missing provenance.
- Prerequisite owners: [`TemporalFormat.lean`](../A12Kernel/Semantics/TemporalFormat.lean), [`FullDate.lean`](../A12Kernel/Semantics/FullDate.lean), [`DateTime.lean`](../A12Kernel/Semantics/DateTime.lean), [`BerlinLegacyTimeZone.lean`](../A12Kernel/Semantics/BerlinLegacyTimeZone.lean), the comparison/aggregate/difference owners, and checked numeric-source/expression owners. Dynamic inputs receive an explicit `World`.
- Unresolved source fact: compose one dynamic `AddDays(Now, amount)` result into one checked `AddHours`/`AddMinutes`/`AddSeconds` with explicit per-call `World`, retaining calendar-then-elapsed order, exact instant, milliseconds, omission, and cause order. The peer's adjacent day probes still do not calibrate the source-offset/refit mechanism, which remains pending under [`SPEC-2026-07-29-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-07-29-01). Wider formats, legal zones/pre-floor identities, detailed basic-check errors, repeatable placement, broader recursive lowering, and date-like distinct-count identity remain open.
- Most dangerous discriminator: equal Berlin wall labels can denote different instants, and another `World` can change `Now`. Wall-label-only identity, early clock resolution, or elapsed-duration substitution is unsound.
- Consumer hypothesis: Execute, Transform, and Explain must retain instant, source format, decoded components, calendar/profile, world dependency, and target rendering policy. An unsupported zone/profile is explicit insufficiency.
- Forbidden shortcut: do not reuse a day-only operand for sub-day expressions, create a parallel temporal AST, re-resolve an instant, invent target rendering, substitute proleptic dates for an unsupported profile, or equate calendar steps with elapsed duration.
- Evidence status: source and reviewed peer differentials cover broad seams; retained project-local temporal calibration remains sparse.
- Entry gate: each selected temporal family needs one bounded source packet and separating matrix over format, world, profile, gap/overlap/cutover, empty/formal precedence, and target policy.
- Completion gate: every admitted temporal operation and target path is checked across its legal profile with exact empty/formal polarity and separating gap/overlap/cutover/millisecond cases.

### SG7 — String, pattern, and custom-field completion

- Missing invariant: general String ingestion, every String function, pattern admission/execution, Unicode/line-break policy, repeatable lists/requiredness, custom-field output, and String targets must share one checked observation without bypassing normalization or resampling validators.
- Current boundary: [§7](IMPLEMENTATION-MAP.md#7--strings-and-patterns), [§8](IMPLEMENTATION-MAP.md#8--enumerations-and-value-lists), and [String/Enumeration distinct count](IMPLEMENTATION-MAP.md#stringenumeration-distinct-count) own the implemented surface.
- Open: add model-owned checked message-template authoring before raw interpolation; audit remaining grapheme restrictions and surrogate-splitting reachability; source registered-custom and repeatable computed targets before admission.
- Completion gate: every legal String/custom operation and target uses one normalized observation; repeatable/partial consumers preserve exact cause and order; unsupported host capability or syntax fails closed.
- Consumer and evidence: Execute and Explain require normalized text, placement, validator identity, and display bytes. Pattern, Unicode, custom-host, and wider-target calibration remain pending.

### SG8 — Enumeration and value-list completion

- Missing invariant: open/dynamic/partial declarations, remaining repeatable projections, computation filters, RNU authoring, and overloaded value-list consumers must reuse the typed projection and quantifier core without erasing declaration domains.
- Current boundary: [§8](IMPLEMENTATION-MAP.md#8--enumerations-and-value-lists) and [String/Enumeration aggregate counts](IMPLEMENTATION-MAP.md#stringenumeration-aggregate-counts) own the implemented surface.
- Unresolved source fact: table-backed declarations remain unreachable at both the table-name and dependent-column producers; reopen only if either producer appears. Dynamic enumerations are distinct and still require an entry/reachability audit. [`EXP-2026-07-25-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md) owns the reviewed table sweep and its exact revisions.
- Prerequisite: reuse addressed operands, kept-successor traversal, repeatable expansion, and checked RNU topology. Audit dynamic domain ownership and partial declarations before widening.
- Completion gate: every legal declaration profile, projection, domain rule, repeated access, value-list operation, and uniqueness use is checked with display/domain/category distinctions preserved.
- Consumer and evidence: Execute and Transform require positional categories, union admission, many-to-one identity, and directional empty/unknown behavior. Broader §8 portable calibration remains open.

### SG9 — paths, indices, and static legality completion

- Missing invariant: bilingual parser/renderer paths, lexical/dot syntax, semantic indices, globals, nested/multiple stars, wider RNU `@From`, and remaining diagnostics must resolve through one checked namespace.
- Current boundary: [§10](IMPLEMENTATION-MAP.md#10--paths-and-references) owns the implemented path surface.
- Prerequisite owners: [`Flat.lean`](../A12Kernel/Elaboration/Flat.lean), [`StarPath.lean`](../A12Kernel/Elaboration/StarPath.lean), [`SingleGroup.lean`](../A12Kernel/Elaboration/SingleGroup.lean), and [`SemanticIndex.lean`](../A12Kernel/Elaboration/SemanticIndex.lean).
- Unresolved source fact: mine bilingual lexical/renderer roundtrip, globals, nested/multiple semantic-index ownership, wider RNU `@From`, and diagnostic precedence in coherent batches.
- Most dangerous discriminator: bare name, parent walk, and named turning point can spell neighboring routes under different rules; equal local indices under different outer rows remain distinct; unavailable index columns have phase-specific effects.
- Consumer hypothesis: Translate, Transform, and Explain require stable declaration/row identity, preserved authored path distinctions, and exact static failure classes.
- Forbidden shortcut: no string-splitting semantics, invented quoting/case, first ambiguous match, flattened row identity, or UNKNOWN for structural failure.
- Entry gate: complete one bounded source packet and separator matrix for the selected path/index family.
- Completion gate: every legal reference resolves deterministically, every illegal form receives the correct static class, and rendering round-trips for the supported surface.

### SG10 — message construction and formal-output integration

- Missing invariant: authored template parsing, token legality, path/star/index/category/`BaseYear` lookup, locale/display providers, format errors, custom output, repeatable pointers, and validation/computation orchestration must produce exact structured messages without changing firing.
- Current boundary: [§13](IMPLEMENTATION-MAP.md#13--message-interpolation) and [§12](IMPLEMENTATION-MAP.md#12--validation-and-polarity) own the implemented rendering/attachment surface. SG4 owns computation pointer partition.
- Unresolved source fact: audit tokenization/invalid precedence, locale/display, field format errors, category/index/`BaseYear` lookup, custom output, repeated pointers, `NumericTargetError` formal codes, and rendering orchestration.
- Most dangerous discriminator: inserted bytes containing delimiters stay opaque, and a message exists only after its verdict/transition fires.
- Consumer hypothesis: Explain and Govern require structured provenance, pointers, exact bytes, severity, and polarity; missing providers/pointers are explicit insufficiency.
- Forbidden shortcut: no repeated replacement, reparsing inserted bytes, invented fallback, second lookup path, pre-verdict attachment, or formatting back-effect.
- Entry gate: complete one source packet and separator matrix for the selected message family.
- Completion gate: legal routes render with exact order/locale/pointer/severity/polarity; invalid templates fail at authoring and messages have no semantic back-effect.

### SG11 — custom-condition checked orchestration

- Missing invariant: registration, static restrictions, effective data/relevance/formal/pointer construction, host call order, messages, and whole-rule integration must surround the pure reached-leaf oracle without unsupported locality or monotonicity laws.
- Current boundary: [§14](IMPLEMENTATION-MAP.md#14--custom-conditions) owns the pure successful callback leaf.
- Prerequisite: checked document supplies data and SG10 supplies formal output. Host failures remain explicit integration outcomes unless Kernel behavior establishes otherwise.
- Completion gate: checked authoring/orchestration reproduce registration, eligibility, projection, order, failure, and message behavior while retaining current non-laws.
- Consumer and evidence: Execute and Qualify require a concrete host contract and observable call discipline; project-local orchestration evidence is pending.

### SG13 — group-list and group-count completion

- Missing invariant: every group-list predicate and filled-group count must reuse the resolved group product or structural terminal-row count while preserving partial relevance, wildcard expansion, filter order, computation poison, and decisiveness.
- Current boundary: [resolved validation group presence](IMPLEMENTATION-MAP.md#resolved-validation-group-presence) and [checked group-star terminals](IMPLEMENTATION-MAP.md#checked-group-star-terminals) own the implemented surface.
- Prerequisite owners: [`GroupPresence.lean`](../A12Kernel/Semantics/GroupPresence.lean), [`CheckedGroupPresence.lean`](../A12Kernel/Elaboration/CheckedGroupPresence.lean), [`StarGroup.lean`](../A12Kernel/Elaboration/StarGroup.lean), and shared validation/computation traversal.
- Unresolved source fact: audit partial fixed/starred multi-entity lists, filtered group operands, and computation group counts, including relevance timing and poison/lookahead policy.
- Most dangerous discriminator: nonrelevant content or a later failed expansion beside an earlier decisive group separates eager, leaking, and correct prefix accounts.
- Consumer hypothesis: Execute/Explain require exact product/count, relevance, environment, and reached failure; Analyze requires operand order and decisive prefix.
- Forbidden shortcut: no caller-supplied relevance on a full document, accidental validation/computation scan sharing, row inference from patterns, or UNKNOWN/poison for structural failure.
- Entry gate: select one result-domain family and show existing product/tally/traversal owners express every observed branch.
- Completion gate: every admitted direct/list/starred/partial/filtered/count consumer delegates to the established owner with exact order, relevance, error, polarity, and poison behavior.

## Scope questions

<a id="scope-questions-not-yet-obligations"></a>
<a id="scope-questions--not-yet-obligations"></a>

### SQ1 — is mandatory-information derivation part of the targeted language?

- Status: open scope question, not yet an obligation.
- Basis: a12-dmkits `ee2f5d84` found one `FeldOperationUtil.getZahlKonstanteWert` `-1` sentinel conflation in mandatory-information comparison derivation; colliding literals include `-1`, `4294967295`, and `8589934591`.
- Decision required: if mandatory-information derivation is in scope, model the caller asymmetry and probe its observable output; if out of scope, state the exclusion in [`SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md).
- Blocking: nothing. Decide scope before requesting an oracle observation.

## Cross-family conformance gap

### SG12 — retained Kernel correspondence coverage

- Missing invariant: every implemented family ultimately needs versioned retained observations that distinguish realistic wrong accounts; source reading, internal proofs, and peer agreement are not Kernel calibration.
- Current boundary: [`EVIDENCE.md`](EVIDENCE.md) and the [external-evidence gate](IMPLEMENTATION-MAP.md#current-external-evidence-gate) own the exact retained inventory and limits.
- Prerequisite owners: [`EVIDENCE.md`](EVIDENCE.md), [`ObservationBundle.lean`](../A12Kernel/Evidence/ObservationBundle.lean), typed projections, and the [`compact semantic-evidence pipeline`](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md).
- Unresolved source fact: for each coherent internally closed family, determine whether an unchanged source-owned a12-dmkits route emits the needed observation shape; otherwise request only the smallest missing producer capability.
- Most dangerous discriminator: a happy path compatible with both the chosen and a realistic wrong account does not calibrate the seam.
- Consumer hypothesis: Qualify/Govern require Kernel version, producer revision, digest, typed replay, separator, and finite claim limit.
- Forbidden shortcut: no source/peer/proof-as-evidence, universal claim from finite cases, resurrected universal capture estate, per-capsule harness, or copied sibling patch.
- Entry gate: select one coherent family at a capability milestone and define its wrong-account matrix and exact retained claim.
- Completion gate: every correspondence claim cites retained observations with provenance, separators, replay, and explicit finite limits; mismatches correct the theory or open a divergence.
