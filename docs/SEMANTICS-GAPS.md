# Open semantic gaps

This is the open-only work index for convergence toward complete semantic conformance with A12 kernel 30.8.1. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) remains the detailed owner of implemented, proved, externally calibrated, protocol-exposed, and consumer-probed coverage; [`PLAN.md`](PLAN.md) selects the immediate unit from this index.

## Lifecycle

- A gap exists here only while a kernel behavior, required static legality rule, checked construction, or conformance obligation remains open. Completed gaps are deleted in the completing commit; Git records when they closed, while the resulting capability and evidence status remain in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).
- `SG<n>` identifiers are never reused. Before assigning one, search this repository and Git history. A durable conclusion discovered while closing a gap belongs in the relevant [`spec/`](../spec/) clause or, for a non-obvious formalization consequence, [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md).
- Each gap states the missing invariant, current boundary, prerequisite, completion gate, named consumer consequence, external-evidence state, and a reopening trigger when blocked or deferred. It does not repeat completed inventories, gate counts, implementation narratives, or immediate scheduling.
- A blocked entry remains here with the exact missing fact or shared boundary and a reopening trigger. A protocol, shipment, dependency, harness, or governance proposal is not a semantic gap and remains with its existing owner and approval rule.

## Keystone construction gaps

### SG1 — general checked document construction

- Missing invariant: one model-owned route must derive raw cell placement, present-empty transport, group content, formal-check context, and phase observations from a general `Document` without consumer-specific adapters.
- Current boundary: flat nonrepeatable contexts, typed temporal payloads, prepared custom String checking, one raw one-group view, and resolved group-presence inputs are closed independently; see [§3](IMPLEMENTATION-MAP.md#3--formal-checking-and-phase-observation), [§4](IMPLEMENTATION-MAP.md#4--required-property), and [resolved group presence](IMPLEMENTATION-MAP.md#resolved-validation-group-presence).
- Prerequisite: audit the document/model ownership of instantiated rows, group content, custom-validator caching, and generated findings before choosing a single construction boundary. Do not infer row existence from nonempty cells.
- Completion gate: checked flat, required/group-presence, custom-field, repeatable, and partial-validation consumers receive coherent views from the same general document route; wrong IDs, kinds, scopes, and malformed placement fail closed; the route has an executable separating matrix and model/context coherence laws.
- Consumer and evidence: Execute and Explain consumers need stable addresses and exact empty/formal distinctions. Existing compact validation evidence covers only narrow flat cases; broader correspondence is pending a coherent input-construction calibration.

### SG2 — general repeatable addressing and operand construction

- Missing invariant: authored paths, repeatable scopes, actual row identities, reopened nested levels, filters, and per-source declaration metadata must produce one ordered resolved operand stream and hierarchical omitted-tail state without flattening parent/child structure.
- Current boundary: one exact one-level finite Number star, one checked correlation shape, checked model-owned general group-star path lowering, general `Document`-to-nested-tree/ordered-`Env` resolution, unfiltered and resolved-validation-`Having` nested Number cell streams with contextual over-repetition classification, both all-rows wildcard relevance and order-aware per-cell partial `FirstFilledValue` relevance for that source, caller-supplied RNU rows, and resolved group presence are closed. The resolved validation filter keeps candidate order, separates complete candidate and captured environments, and reads only retained targets. All-rows and per-cell gates share path/index patterns but preserve their distinct operator decisions; computation-filter poison/dependency and multi-operand per-slot encounter remain open. See [§9](IMPLEMENTATION-MAP.md#9--repetition-and-iteration), [reopened-star completeness and addressing](IMPLEMENTATION-MAP.md#reopened-star-structural-completeness-and-addressing), and [resolved Number `FirstFilledValue`](IMPLEMENTATION-MAP.md#resolved-number-firstfilledvalue).
- Prerequisite: next obtain the shared checked condition/expression tree from SG3, then lower general authored filters, mixed declarations, and multi-operand `FirstFilledValue` without introducing a second row tree, cell parser, condition evaluator, or aggregate scan. Reuse `SingleGroup`, `ReopenedStarDomain`, `ResolvedStarTopology`, the general environment selector, `RelevantEntityPattern`, `ValueListCell`, and the nested Number route. Before claiming the complete partial-validation boundary, audit whether absent or phantom declared rows require identity beyond the current hierarchical omitted-tail marker.
- Completion gate: nested and multiple stars, filters, partial relevance, cross-level references, mixed metadata, aggregates, value lists, `FirstFilledValue`, RNU, and group-presence consumers share one checked construction route with tree/stream correspondence laws and separators at every reopened level.
- Consumer and evidence: Execute, Transform, and Explain consumers require stable row identity, encounter order, and wildcard/concrete relevance distinctions. IF42, IF193, IF194, and one-level aggregate differentials provide triangulation; project-local general repeatable evidence remains pending.

### SG3 — shared checked condition and expression tree

- Missing invariant: whole-rule validation, numeric comparisons, generated implicit validation, aggregate expressions, and computation-table guards must share one checked condition representation and evaluator rather than parallel flat and numeric trees.
- Current boundary: `ConditionTree` owns connective shape, empty-row eligibility, reference traversal support, static all-leaf admission, and exact verdict-aware short-circuit evaluation. `FlatCondition` is that tree over flat leaves, while `ValidationCondition` admits flat and resolved numeric-comparison leaves in one tree with shared evaluation, field-reference traversal, and per-leaf relevance. `CheckedValidationCondition` lifts only checked flat/numeric inputs, preserves the exact common row group, rejects mismatches, and carries model/core coherence. `ResolvedRule` and `CheckedResolvedRule` parameterize the existing metadata/error-field certificate and sole post-verdict message emitter. `NumericOperandScope` now preserves ordinary same-group admission and computation's model-wide nonrepeatable admission as explicit policies on the same comparison certificate. One checked unconditional operation is narrowed without surface reconstruction, joined to the target-filled gate in the mixed tree, and emitted through the shared whole-rule boundary; cross-group Number and temporal-component cases separate it from ordinary validation. Literal guarded tables remain separate, and resolved aggregates are not expression nodes. See [§5](IMPLEMENTATION-MAP.md#5--numbers-and-decimals), [§11](IMPLEMENTATION-MAP.md#11--computations), and [§12](IMPLEMENTATION-MAP.md#12--validation-and-polarity).
- Prerequisite: reuse the existing nonempty table/cardinality representation and operation-neutral selector at the second payload consumer so every checked numeric-expression alternative produces a guarded mismatch, the optional common guard remains once outside the declaration-ordered disjunction, and tolerance stays validation-only. Do not add a generated-only comparison wrapper, re-elaborate resolved operations through guessed surface syntax, or merge validation evaluation with first-match computation. Then add aggregate expression nodes rather than bypassing the tree.
- Completion gate: one checked tree admits the established flat and numeric leaves plus aggregate nodes, drives whole-rule and generated-rule evaluation in both phases, exposes one reference/relevance traversal, and derives old fragment laws by specialization. No aggregate-only comparison wrapper or second scale gate remains.
- Consumer and evidence: Transform and Compile consumers need one syntax-preservation relation and explicit unsafe rewrites. Existing numeric, generated-rule, and aggregate evidence is fragmented; calibration remains family-batched after the shared representation closes.

### SG4 — computation scheduling and state transition

- Missing invariant: authored computation tables, generated validations, dependency order, poison/clearing, repeatable targets, missing-ancestor creation, and exact target application must compose as one document transition system.
- Current boundary: resolved first-match tables, selected String operations, checked plain Number operations, target/delta/application, common preconditions, and literal generated validation are closed separately; see [§11](IMPLEMENTATION-MAP.md#11--computations).
- Prerequisite: SG1 supplies document state, SG2 supplies repeatable addressing, and SG3 supplies shared guards and expression-valued generated validation. Source-audit scheduling, transitive dependencies, joins, and result-empty provenance before defining transitions.
- Completion gate: an executable checked scheduler produces deterministic document states and exact findings for every admitted target kind and scope; laws cover order, locality, poison absorption, clearing, dependency stability, and independent transitions; adversarial cases separate target self-reference, first poison, missing ancestors, and repeatable addressing.
- Consumer and evidence: Execute, Compile, Analyze, and Explain consumers require explicit transition traces. Current evidence covers isolated target and selection seams, not scheduling or whole-document transitions.

## Semantic-family gaps

### SG5 — numeric authoring and target completion

- Missing invariant: the existing numeric evaluator must cover the kernel's remaining authoring shapes, wrapper traversal, computation power, aggregate nodes, Date/aggregate extrema overloads, rendering, target-policy construction, and partial/repeatable integration through the shared owners.
- Current boundary: plain arithmetic/power, direct-root `Round`/`Abs` and bounded `Min`/`Max`, tolerance, stored conversion, complete resolved Number target policy, exact application, and narrow checked validation/computation are implemented; see [§5](IMPLEMENTATION-MAP.md#5--numbers-and-decimals).
- Prerequisite: SG3 for expression-valued whole-rule/generated integration, SG2 for repeated operands, and declaration-owned model facts for target-policy construction. Audit broader wrapper legality and result-empty provenance rather than assuming compositional admission.
- Completion gate: every legal numeric operator and authoring region is checked and executable in validation and computation where the kernel permits it; illegal shapes fail with the right static class; target rendering/application and fillability retain their existing discriminators.
- Consumer and evidence: Execute and Transform consumers need exact tree shape, rounding stages, target policy, and unsafe reassociation boundaries. Current operator differentials are broad but project-local portable coverage remains partial.

### SG6 — temporal authoring, calendar, and target completion

- Missing invariant: general temporal parsing/admission, construction forms, model-zone legacy calendar stepping, additions/differences, DateRange operations, partial/formal propagation, and stored/computed temporal targets must preserve exact instant, decoded component, format, and calendar provenance together.
- Current boundary: checked direct comparisons and numeric components, exact `Now`, model-zone `Today`/`BaseYear`, stored full-Date shifts and month/year differences, resolved extrema/range overlap, Berlin's versioned offset profile, and a finite `DifferenceInDays` spring slice are implemented; see [§6](IMPLEMENTATION-MAP.md#6--dates-and-time), [Date construction](IMPLEMENTATION-MAP.md#resolved-three-part-date-construction-and-base-year-date-sources), and [`DifferenceInDays`](IMPLEMENTATION-MAP.md#differenceindays-finite-profile-closure).
- Prerequisite: establish declaration-owned format/rendering/value-admission policy for Date/DateTime targets and a general model-zone hybrid-calendar landing account. Do not substitute proleptic `CivilDate` or exact elapsed duration for kernel calendar identity.
- Completion gate: every admitted temporal operator, construction, comparison, aggregate, difference, shift, range, and target path is checked across legal zones/formats with exact empty/formal polarity; gaps, overlaps, cutover dates, partial dates, and millisecond identity have separating laws and cases.
- Consumer and evidence: Execute, Transform, and Explain consumers need both exact-instant and source-format/calendar distinctions. Existing temporal source and peer differentials are extensive, but retained project-local observations remain sparse and should be batched by comparison, arithmetic, and target families.

### SG7 — String, pattern, and custom-field completion

- Missing invariant: general String ingestion, every String function, pattern admission/execution, line-break and grapheme policy, repeatable lists/requiredness, custom-field validation output, and String target construction must share the checked String observation without bypassing normalization or resampling validators.
- Current boundary: direct comparison, `Length`, presence/requiredness, CRLF normalization, flat value lists/membership, resolved pattern consumption, scalar String expressions, one positive target length bound, prepared custom validation, exact custom formal-message projection, and resolved RNU bridging are implemented; see [§7](IMPLEMENTATION-MAP.md#7--strings-and-patterns).
- Prerequisite: retain declaration-owned length/line-break policy in the flat model, define the document-addressed one-physical-call custom-validator cache through SG1, and audit the remaining Java-pattern and grapheme admission restrictions before widening checked lowering.
- Completion gate: every legal String/custom operator and target policy executes through one normalized observation; repeatable and partial consumers preserve exact causes and encounter order; custom validity/messages/orchestration reuse the same sampled result; wrong host capability or unsupported syntax fails closed.
- Consumer and evidence: Execute and Explain consumers need normalized text, source placement, exact validator identity, and resolved display bytes. Existing String cascade evidence is strong for narrow targets; pattern, Unicode, custom-host, and wider target correspondence remain pending.

### SG8 — Enumeration and value-list completion

- Missing invariant: table/open/dynamic/partial Enumeration declarations, repeatable category access, expansion/filtering, RNU authoring, and remaining kind-overloaded value-list consumers must reuse the type-indexed projection and quantifier core without erasing declaration domains.
- Current boundary: ordinary closed declarations, stored/category scalar comparison, String/Enumeration direct comparison, scalar and multi-field literal/field-valued membership, and checked RNU components are implemented for nonrepeatable flat fields; see [§8](IMPLEMENTATION-MAP.md#8--enumerations-and-value-lists).
- Prerequisite: SG2 for repeatable expansion and checked RNU scope/topology; audit dynamic/table domain ownership and partial declaration behavior before changing the closed declaration proof.
- Completion gate: every legal declaration profile, projection, literal/domain admission rule, repeated access, value-list operator, and uniqueness use is checked with display/domain/category distinctions preserved; invalid combinations fail at the kernel-equivalent layer.
- Consumer and evidence: Execute and Transform consumers require positional category mapping, union admission, many-to-one identity, and directional empty/unknown behavior. The bounded cold probe passed for the closed nonrepeatable fragment; portable §8 evidence and broader profiles remain open.

### SG9 — paths, indices, and static legality completion

- Missing invariant: parser/renderer paths, parent and bare resolution, quoted/named references, `RuleGroup`, semantic indices, globals, nested/multiple-star lookup, RNU `@From`, and every required static diagnostic must resolve through one checked model namespace.
- Current boundary: nonrepeatable flat paths, one absolute/direct-child relative star/correlation form, unique ID/path lookup, shared parent walking, and one resolved literal-key semantic-index Number consumer are implemented; see [§10](IMPLEMENTATION-MAP.md#10--paths-and-references).
- Prerequisite: SG2 for repeatable scopes and SG1 for document/index materialization. Mine the parser grammar, model API, and static check owners in coherent batches rather than adding diagnostic-specific path functions.
- Completion gate: every legal reference form resolves deterministically to its scope and every illegal form receives the correct static class; semantic-index presence/value/fill consumers share normalized key and unavailable-column state; path rendering round-trips for the supported language-neutral surface.
- Consumer and evidence: Translate, Transform, and Explain consumers need stable reference identity and legality diagnostics. Current evidence covers narrow flat/correlation paths and resolved index behavior only.

### SG10 — message construction and formal-output integration

- Missing invariant: authored template parsing, token legality, path/star/index/category/`BaseYear` lookup, locale/display providers, field-owned format errors, custom-condition output, repeatable pointers, and validation/computation orchestration must produce exact structured messages without changing firing semantics.
- Current boundary: parser-independent one-pass interpolation after resolved lookup, fired-only flat/generated-rule integration, and one custom-field formal-message projection are implemented; see [§13](IMPLEMENTATION-MAP.md#13--message-interpolation) and [§12](IMPLEMENTATION-MAP.md#12--validation-and-polarity).
- Prerequisite: SG1/SG2/SG9 supply addressed values and scopes; declaration-owned display/format providers must be explicit. Preserve opaque inserted bytes and never reparse generated text.
- Completion gate: all legal tokens and message routes render with exact order, locale, pointer, severity, polarity, and fallback behavior; invalid templates fail at authoring; messages are emitted only after the owning verdict/transition fires and have no semantic back-effect.
- Consumer and evidence: Explain and Govern consumers require stable structured provenance plus user-facing bytes. Existing compact validation/String evidence covers only small message slices.

### SG11 — custom-condition checked orchestration

- Missing invariant: registration/name resolution, static restrictions, effective data/relevance/formal/pointer construction, host call order, messages, and whole-rule integration must surround the existing pure reached-leaf oracle without granting unsupported locality or monotonicity laws.
- Current boundary: one successfully registered, already-reached pure total callback leaf is represented with four abstract channels and exact true/false projection; see [§14](IMPLEMENTATION-MAP.md#14--custom-conditions).
- Prerequisite: SG1 supplies the concrete document view, SG3 supplies whole-rule placement, and SG10 supplies formal output. Define host failures as explicit integration outcomes rather than semantic UNKNOWN unless kernel behavior establishes otherwise.
- Completion gate: checked authoring and runtime orchestration reproduce registration, eligibility, data projection, call order, error handling, and message behavior while retaining the existing non-laws; platform-specific host adapters remain outside the pure theorem root.
- Consumer and evidence: Execute and Qualify consumers need a concrete host contract and observable call discipline. Source and a12-dmkits controls anchor the leaf; project-local orchestration evidence is pending.

## Cross-family conformance gap

### SG12 — retained kernel correspondence coverage

- Missing invariant: every implemented semantic family ultimately needs versioned retained observations that distinguish its realistic wrong accounts; source reading, internal proofs, and peer agreement alone do not establish kernel correspondence.
- Current boundary: 51 private compact observations and 25 public associations cover selected flat validation, correlation, String computation, and direct-cascade cases; the exact inventory and limits live in [`EVIDENCE.md`](EVIDENCE.md) and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md#current-external-evidence-gate).
- Prerequisite: batch only coherent closed families, reuse an unchanged source-owned a12-dmkits route when its observation shape fits, and request the smallest upstream producer capability only when no suitable route exists. Never recreate the retired universal capture estate.
- Completion gate: each implemented clause's correspondence claim cites a retained kernel observation set with provenance, separating controls, replay, and explicit finite limits; mismatches correct the theory or open a documented divergence.
- Consumer and evidence: Qualify and Govern consumers need auditable provenance. Calibration batches follow semantic family milestones and do not block unrelated Tier 1 internal closure.
