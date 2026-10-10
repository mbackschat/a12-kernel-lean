# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns open `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. Terminal receipts leave this queue after their useful live facts are preserved in the canonical spec, source or gap owner.

The terminal receipts retired on 2026-10-10 remain in [the ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), under their stable entry anchors. Earlier deleted receipts remain in [the historical ledger](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md) and [the accepted receipts through 2026-09-24](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md) at `a050f150`. Recover any exact receipt with `git show <revision>:<path>` and find its stable ID; retired IDs are never reused.

## Ledger contract

Every commit that corrects, narrows, or extends kernel behavior in `spec/` and still needs a12-dmkits reconciliation must add or update an entry here in the same change. The spec clause owns the complete semantic account; an entry links to that clause and records only the transport facts needed by a12-dmkits.

An inbound correction whose exact source revision is already committed and reviewed in a12-dmkits does not create a new outbound entry. Record that revision and its evidence route in [`SOURCES.md`](SOURCES.md). If the inbound result answers an existing `pending` or `handed-off` entry, update that same entry instead.

Pure spelling, formatting, link, and non-semantic navigation edits do not enter the ledger. One entry may group several clauses only when they express one coherent behavioral correction with one upstream acceptance decision.

Each entry has a stable `SPEC-YYYY-MM-DD-NN` or `EXP-YYYY-MM-DD-NN` ID that is unique across the live queue and its retired Git history. IDs are never reused. An entry records its exact status, canonical clause or experiment question, concise delta, evidence basis and kernel version, expected reconciliation surfaces, acceptance condition, local introducing revision, and reviewed a12-dmkits revision and disposition when terminal. A later correction creates a new entry with `Supersedes`; it never rewrites a terminal receipt.

Statuses are exactly `pending`, `handed-off`, `accepted`, `answered`, `resolved`, `rejected`, or `superseded`. `accepted` requires review of an exact a12-dmkits revision against the entry's acceptance condition. `resolved` is only for an `EXP-` closed locally without an upstream observation. **`answered` is for an entry the peer engaged whose outcome is neither acceptance nor refutation**, and it exists because four entries reached exactly that state and the six-status list could not express any of them: an `EXP-` closed *by* an upstream observation rather than locally, and a `SPEC-` where the peer could not corroborate in the way its own acceptance condition anticipated, or found reconciliation unnecessary, or stated a free choice not to carry it. An `answered` entry owes nothing in either direction and carries a `disposition` or `answered` row saying which of those it was; do not relabel one as `accepted`, which asserts an acceptance review that never happened. An inconclusive handback remains `handed-off`. Contrary kernel evidence prevents acceptance and requires the local semantic account to be corrected before the entry is rejected or superseded.

The user transfers pending entries. Treat the entire `../a12-rulekit/` checkout as read-only. Reconciliation here means inspecting an exact committed a12-dmkits revision and recording the reviewed outcome in the existing entry. Do not create a second feedback ledger. A `dmtool-release` instrument defect goes to the a12-dmkits session directly, or to a dated feedback note under the user's exchange directory when no such session is reachable, as defined by [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback); neither belongs in this ledger.

The introducing revision cannot name itself inside the same commit. Until handoff, `introducing commit` means the first commit containing the stable entry ID; resolve it with:

```sh
git log --reverse -S 'SPEC-YYYY-MM-DD-NN' --format='%H' -- docs/A12-DMKITS-SPEC-SYNC-LEDGER.md | head -n 1
```

An exact a12-dmkits revision must resolve when its handback is reviewed. If later upstream history rewriting makes it unreachable, retain the historical citation, do not invent a replacement mapping, and re-discharge any reused claim against the maintained owner at the then-current reviewed revision. The measured boundary and claim limit are the older receipt file's `#receipt-continuity` section at that revision.

## Entry kinds and routing

- **`SPEC-…`** records a locally originated semantic correction that still needs a12-dmkits reconciliation. A locally measured static-legality finding is a `SPEC-`, not an experiment request.
- **`EXP-…`** requests one specific kernel-runtime observation only after the available local source, static-check, retained-evidence, and runtime-probe routes have been checked and shown unable to settle it. State the exact input, competing accounts, prediction under each account, negative result, and route limit. If no input distinguishes the accounts, the entry is not ready.
- **The user carries pending entries to a12-dmkits.** Prepare the stable ID and its checkpoint anchor in the same change. Do not send entries to peer sessions automatically; reconcile the exact committed handback when the user supplies it, following [the repository authority](../CLAUDE.md#%EF%B8%8F-hard-rule--request-a12-dmkits-improvements-upstream-never-patch-a-copied-harness).
- **The routing test is one question: is kernel behavior in question, or only this project's ability to observe it?** A `dmtool-release` command, schema, diagnostic, exit, or artifact defect is instrument feedback rather than kernel semantics: it goes to the a12-dmkits session directly or, when none is reachable, to a dated feedback note in the user's `~/Downloads` exchange directory per [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback), and **never to this ledger**, because a note has no acceptance condition or reviewed-revision receipt. A missing tool capability that blocks a measurement is such a note, while the semantic question it blocks is an entry. A cross-project capability or retirement request follows the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule).

[`SOURCES.md`](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) owns the current observation-route inventory and [`TESTING.md`](TESTING.md#the-kernel-runtime-probe-route) owns its method. Every claim leaving this repository must also satisfy the discharge rule in [`../CLAUDE.md`](../CLAUDE.md#%EF%B8%8F-hard-rule--discharge-a-claim-before-stating-it-or-flag-it-and-surface-it).

## Current queue

<a id="spec-2026-10-10-01"></a>
### SPEC-2026-10-10-01 — explicit narrower guards qualify target-derived operand scope

- `status`: pending
- `canonical`: [computation formal inputs](../spec/09-computations.md) and [filter cache scope](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation) derive target subtrees from guard preprocessing, not an unconditional target expansion.
- `delta`: the implicit nearest-repeatable-group guard is omitted when an authored computation already has a conditional-group profile protecting that row or a narrower containing group. A narrower guard can exclude outer siblings from expanded operand scope; explicit row guards still include them. Computed fields stay excluded from formal inputs.
- `basis`: [three-model Kernel 30.8.1 matrix](sources/computation-scheduling-probes.md#src-computation-guard-operand-scope), 15 agreeing runtime rows, plus the source-owned common mechanism. Formal findings do not prevent the target computing. Cache consequences are source-derived, not newly runtime-measured.
- `acceptance`: reconcile KF538's blanket target-subtree account and operand/cache collection with implicit, explicit-row and narrower-containing-group controls. Preserve per-authored-computation preprocessing and distinguish scheduling dependencies from operands. Retain nested/sparse/partial-validation limits. Introducing revision is the first commit containing this ID; no reviewed peer response yet.


<a id="spec-2026-10-10-02"></a>
### SPEC-2026-10-10-02 — consumer-specific sparse filter traversal above 100 candidates

- `status`: pending
- `canonical`: [filter traversal](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation).
- `delta`: Sparse-enabled consumers use phase-visible coordinate-prefix occupancy above 100 cache-bounded candidates. Initial/reset searches remain dense until a candidate is kept; rejection does not advance the kept cursor. Computation retains successor lookahead. First-filled, value counts and any-pair overlap remain dense; scalar-versus-list overlap opts into sparse traversal.
- `basis`: [Kernel 30.8.1 computation matrices and source account](sources/group-and-iteration-probes.md#src-sparse-filter-traversal), both strategies agreeing. Sum/filled count, threshold/reset/occupancy controls, Number/String/Boolean value counts and exact/yearless overlap policies are measured. Distinct/extrema extensions and full validation remain source-derived.
- `field-fill extension`: The five-row, seven-operator Kernel matrix now confirms these policies on computation and full validation: positive presence is sparse-enabled; negative presence, second-witness and declared-empty are dense. Both phases use kept-successor lookahead and can decide before a later filter failure. Composite guards restart with the appropriate policy. The full-validation adapter now consumes incrementally; an eager materialized filter selection is not equivalent. Wider carrier/profile calibration and other predicate/membership prefix adapters remain pending.
- `uniqueness extension`: [Uniqueness](../spec/07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules) remains dense on both arms and preserves successor lookahead before deciding at a duplicate. Full validation compares incrementally, so a duplicate hides later filters and authored operands. The source route is settled; new large-domain and validation-prefix external calibration remains pending.
- `membership extension`: The [six-row membership matrix](sources/group-and-iteration-probes.md#src-sparse-filter-traversal) confirms sparse collection/search for AtLeastOne and dense passes for No/NotAll. The [membership clause](../spec/06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-) now preserves ordinary NotAll's presence short circuit before a failing filtered values side. Reconcile KF68's equivalence claim at the pure-member boundary; it does not authorize eager filtered collection. Number/String both-arm calibration is retained; optimized OL emission, wider carriers and partial validation remain bounded separately.
- `first-filled extension`: The [seven-row, five-profile matrix](sources/group-and-iteration-probes.md#src-sparse-filter-traversal) confirms dense first-filled scans in both arms, including domains above 100, reached successor failure, hidden later filters and termination on unavailable payloads. Reconcile full-validation adapters that materialize all filtered candidates and computation comparison carriers that refuse large or filtered sources. Enumeration, other temporal formats, direct result-assignment admission and partial validation remain separately bounded.
- `reconcile`: iteration prose and consumer-specific evaluator traversal. Preserve the distinction between candidate cache scope, occupancy, filter execution and payload consumption; do not replace it with physical-row filtering.
- `acceptance`: Review the canonical account against the retained matrix and source, reconcile the peer's supported surfaces, and state remaining predicate/prepass, partial-validation and external-calibration limits explicitly.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

<a id="spec-2026-10-10-03"></a>
### SPEC-2026-10-10-03 — selected error references retain authored identity and scope

- `status`: pending
- `canonical`: [ordinary iteration and error references](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) distinguish selected payloads, authored keys and implicit index-cache dependencies.
- `delta`: A selected payload does not bind its selected row level, but retains ordinary ancestor bindings. A field-valued key keeps its own scope. Merely consulting the index column does not name that field for static error-field admission; explicitly selecting or guarding it does.
- `basis`: [Source checkpoint](sources/having-filter-probes.md#src-having-reference-scope), from authored entity-map insertion through semantic-index coordinate marking to error-reference classification. Local reader controls cover independent field/group callers and admitted twins; this extension has no new Kernel capture.
- `acceptance`: Reconcile static membership and per-level iteration separately from runtime dependency/message sets. Check selected field and group payloads, literal/field keys, explicit-index twins, bound ancestors, sibling versus own-error guards and unchanged computation admission. Introducing revision is the first commit containing this ID; no peer response yet.


<a id="spec-2026-10-10-04"></a>
### SPEC-2026-10-10-04 — numeric parallel lookup aliases can produce repeated visits

- `status`: pending
- `canonical`: [Parallel iteration](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key) separates rendered iteration-token identity from numeric lookup identity.
- `delta`: Equal Number values still match across declarations with different minimum fractional digits, but distinct rendered tokens both visit the same matched pair. Deduplicating by numeric value loses observable message multiplicity; treating the tokens as unmatched loses lookup semantics.
- `basis`: [Kernel 30.8.1 source and seven-document two-strategy matrix](sources/model-structure-and-declaration-probes.md#src-parallel-number-index-tokens), including positive/negative controls, aligned fractional values, numeric aliases, duplicates and empty groups.
- `reconcile`: Parallel iteration prose and validation evaluator key-union/lookup representation. Preserve duplicate exclusion, invalid-column UNKNOWN and lexical token order; computation target iteration remains a separate consumer.
- `acceptance`: Reproduce one-versus-two matched visits for equal/different minimum scales, one visit when natural fractional precision aligns both renderings, and unchanged unmatched/duplicate controls. State uncalibrated profiles explicitly.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

<a id="spec-2026-10-10-05"></a>
### SPEC-2026-10-10-05 — parallel group operands and duplicate error pointers

- `status`: pending
- `canonical`: [parallel iteration](../spec/07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key) distinguishes group content, parent-local joins and duplicate pointer lookup from value admission.
- `delta`: Group predicates read joined group content after index availability. Common outer coordinates partition key unions. Duplicate value unavailability does not force an unknown error coordinate when another branch fires; pointer lookup retains its separate cache association.
- `evidence`: [Twelve static checks and ten runtime documents](sources/model-structure-and-declaration-probes.md#src-parallel-group-outer), both Kernel strategies. The existing selected-message checkpoint already establishes that physical first/last duplicate order is insufficient.
- `request`: Reconcile the canonical parallel clause and consumer treatment of group references, outer dispatch and duplicate error addresses. No repeated capture is requested.
- `acceptance`: An exact peer revision adopts the distinctions or supplies contrary Kernel evidence. Exact document-to-cache insertion order remains an explicit implementation obligation here.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.


<a id="spec-2026-10-10-06"></a>
### SPEC-2026-10-10-06 — duplicate pointer selection depends on unrelated cache entries

- `status`: pending
- `canonical`: [Selected message coordinates](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages) separate parent-local association identity from whole-cache population order.
- `delta`: An unrelated valid field or empty repeatable group can change the selected duplicate coordinate; empty and malformed field controls do not. An added outer parent can change a parallel error address within another parent. Physical-row order and an index-column-only fold cannot reproduce these observations.
- `basis`: [Ten-document, two-strategy Kernel 30.8.1 matrix and producer source](sources/message-and-pointer-probes.md#src-message-cache-population-order), reusing existing admitted models. Hash-bucket capacity predictions match the selected-reference and parallel-error separators.
- `collision extension`: [Repeated identical inputs](sources/message-and-pointer-probes.md#src-message-cache-collision) produce both duplicate rows within each strategy. Do not require a universally deterministic model/document-only selector; preserve actual host cache order/association. This does not make every duplicate ambiguous.
- `deterministic extension`: The inspected host profile supports never-tree list-bin ties using ascending physical insertion, and reductions whose winners agree across the possible early-resize capacities. [Source and independent host controls](sources/message-and-pointer-probes.md#src-message-cache-population-order) settle the mechanism; the retained no-filler Kernel control confirms its row-1 winner. Tree history and capacity-dependent winners remain explicit limits.
- `query-isolation extension`: [Three-row full/partial controls](sources/message-cache-probes.md#src-message-cache-query-isolation) retain an unresolved collision beside stable selected and parallel coordinates. Keep uncertainty local to the queried group/parent/key while retaining every admitted entry for hash capacity and bin history.
- `request`: Reconcile duplicate-address semantics for both consumers; preserve the separate unavailable value read. No repeated capture is requested.
- `acceptance`: An exact peer revision adopts the distinctions or supplies contrary Kernel evidence; preserve the measured host-dependent collision boundary and retain default, partial-call and other host-profile limits until settled.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

<a id="spec-2026-10-10-07"></a>
### SPEC-2026-10-10-07 — Document JSON compacts surviving object repetitions

- `status`: pending
- `canonical`: [Runtime repetition topology](../spec/07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands) distinguishes JSON conversion from sparse V1 placement padding.
- `delta`: Non-object repetition elements are discarded before assigning consecutive coordinates, independently within each surviving parent. Empty objects remain rows; field-null remains present-empty.
- `basis`: [Nine-document, two-strategy Kernel matrix and source](sources/evaluation-and-application-routes.md#src-json-row-normalization) distinguish null prefix/suffix, mixed non-object kinds, explicit empty rows, two survivors and nested scope.
- `request`: Reconcile consumer JSON ingestion and topology claims against this conversion. No repeated measurement is requested; deserializer diagnostic payloads remain outside this runtime projection.
- `acceptance`: An exact peer revision adopts dense survivor coordinates or supplies contrary Kernel evidence for this route, preserving the separate V1 contract.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

### SPEC-2026-10-10-08 — partial relevance filters message-cache population

- `status`: pending
- `canonical`: [Selected message references](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages).
- `delta`: Partial relevance filters admitted fields and touched ancestor-group placeholders before host ordering. Excluding one unrelated field changes the selected duplicate pointer; retaining just one index row selects that row.
- `basis`: [Seven-row, two-strategy capture and source](sources/message-cache-probes.md#src-message-cache-partial-population), with unchanged full-validation controls.
- `selector extension`: [Topology and excess-selector controls](sources/message-cache-probes.md#src-message-cache-partial-topology) show that an excess descendant selector can retain a valid ancestor cache contribution. Do not discard the entire selector before ancestor projection; capacity gates actual groups/cells. Two nesting depths each have excluded, valid-descendant and excess-descendant controls.
- `request`: Reconcile partial reference-cache production against the filtered population; reuse the retained observations. Keep cache associations separate from duplicate-invalid value reads and from rule-firing gates.
- `acceptance`: An exact peer revision adopts this population boundary or supplies contrary Kernel evidence for the measured carrier; preserve explicit host context where ordering remains unsettled.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

### SPEC-2026-10-10-09 — default cache associations survive index formal invalidity

- `status`: pending
- `canonical`: [Selected message references](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages).
- `delta`: Full calls append singleton defaults after original-population ordering. A formally invalid singleton index may acquire a default message association while its authored read remains UNKNOWN and its formal error persists. Partial calls append none. Empty declared S-value means no default.
- `basis`: [Fourteen-row, two-strategy capture and source](sources/message-cache-probes.md#src-message-cache-default-and-names) cover default staging/capacity and renamed/reserved identifier controls on Kernel 30.8.1.
- `request`: Reconcile message-cache default eligibility separately from evaluation availability; preserve the original population boundary and model-wide name reservations. Reuse the retained observations.
- `acceptance`: An exact peer revision adopts the independent cache/read boundary and name effects or supplies contrary Kernel evidence; no change to invalid-cell authored availability is requested.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

### SPEC-2026-10-10-10 — partial parallel dispatch and frame traversal

- `status`: pending
- `canonical`: [Partial validation](../spec/10-validation-and-polarity.md#5-full-vs-partial-validation).
- `delta`: Parallel dispatch uses compressed error-field selectors, independently of leaf relevance. Concrete joined-row selectors suppress rules with ordinary outer iteration; differing selectors can restore dispatch. Unmatched reads require wildcard index/leaf coverage, and complete descendant coverage can establish group absence. One-sided frames reuse declared-product/occupied-prefix traversal on full and partial calls.
- `basis`: [56-row, two-strategy capture and source](sources/model-structure-and-declaration-probes.md#src-partial-parallel), Kernel 30.8.1; root-repeatability, declaration-location, selector-union, negative-group, duplicate-cache and frame-bound 3/6 twins.
- `request`: Reconcile the parallel dispatch gate separately from key membership and condition visibility; exercise empty frame slots before reusing physical-only traversal. Reuse the retained captures.
- `acceptance`: An exact peer revision adopts these independently measured stages or supplies contrary Kernel evidence. Existing payload-only and excluded-index behavior must remain unchanged.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.

<a id="spec-2026-10-10-11"></a>
### SPEC-2026-10-10-11 — custom validators receive raw text before evaluated normalization

- `status`: pending
- `canonical`: [Custom-field ingestion](../spec/06-strings-and-enumerations.md#a3-custom-field-type-validation) separates original callback input from the accepted evaluated payload.
- `delta`: Validate original stored text, then normalize CRLF once on acceptance. Lone CR survives. Subsequent Length, value and computation reads reuse the checked payload; dependent computations must not re-ingest it. Empty and absent cells bypass validation; ordinary rejected cells remain unavailable.
- `basis`: [Source and eight-row runtime matrix](sources/custom-field-probes.md#src-custom-ingestion), with raw-sensitive/LF-only validators and repeated-CR direct/dependent computation controls. Both Kernel strategies agree. The correction fixes Lean's raw-text acceptance branch; it does not claim an existing peer implementation defect.
- `acceptance`: Reconcile callback-input and evaluated-value contracts on the ordinary stored-document route. Retain separate test-range and conversion-enabled presentation obligations; do not generalize this matrix to arbitrary custom codecs. Introducing revision is the first commit containing this ID; no peer response yet.

<a id="spec-2026-10-10-12"></a>
### SPEC-2026-10-10-12 — measure reserved custom test-range outcomes and continuation

- `status`: pending
- `request`: Supply a retained runtime matrix for a registered validator returning `testIDNummer`, ordinary rejection and acceptance. The [source boundary](sources/custom-field-probes.md#src-custom-test-range) predicts admitted cache text beside a reported finding, but also identifies whole-call continuation and unique-entity interactions. This is a measurement request, not a settled canonical correction.
- `instrument`: The maintained declarative kernelProbe registry exposes only fixed pattern/length error keys. Existing custom rejection-code tests also fix their keys. Use a source-owned differential or extend the maintained observation route; no local harness copy is requested or authorized.
- `matrix`: Cross full/partial validation and computation; direct value/Length reads and seeded copies; unrelated computations; with/without unique entities; full versus abort-on-formal-error validation mode; relevant/excluded, absent and empty controls. Include repeated-CR text to distinguish original callback input from one-pass evaluated normalization.
- `acceptance`: Report exact findings/pointers, available values, changed and unchanged computation outcomes, whole-call abort/fault behavior, and relevant cache membership, separately for both strategies. Pin the producer revision and evidence. Preserve distinctions between observed behavior and source predictions; introducing revision is the first commit containing this ID.

<a id="spec-2026-10-10-13"></a>
### SPEC-2026-10-10-13 — retain empty authored pattern execution failure

- `status`: pending
- `change`: [Pattern execution](../spec/06-strings-and-enumerations.md#pattern-admission-and-execution) distinguishes an admitted empty authored pattern from an inactive empty declared pattern. A reached condition call fails before operand availability, escapes subsequent Boolean conditions and alternative tiers, and is caught by the enclosing validation/computation handler.
- `evidence`: [Source and 56-row matrix](sources/computation-scheduling-probes.md#src-empty-pattern-execution), both strategies agreeing at the pinned clean producer. Direct and Having cases distinguish short circuit, formal-input prepass, partial relevance, empty/uninstantiated candidates, independent targets and nonempty controls. Indexed empty-source behavior is an internal specialization, not measured correspondence.
- `request`: Reconcile consumer execution and canonical prose with this failure effect and its handler boundary. Preserve formal-input precheck precedence and inactive declared-empty policy; do not implement the authored case as a Boolean match result. Introducing revision is the first commit containing this ID.

<a id="spec-2026-10-10-14"></a>
### SPEC-2026-10-10-14 — nested first-filled scans retain empty leading branches

- `status`: pending
- `canonical`: [First-filled selection](../spec/03-empty-and-required.md) retains missing-prefix provenance across nested stars, including an empty or omitted inner group under an earlier parent.
- `delta`: Flattening physical leaf rows loses an observable distinction: a later matching value emits OMISSION after an empty leading branch, while an empty suffix preserves VALUE. Keep visited-prefix missingness separate from omitted-tail metadata.
- `basis`: [Eleven-document, three-carrier matrix](sources/computation-scheduling-probes.md#src-first-filled-empty-prefix) covers String, Number and Boolean full validation with a filtered control, both Kernel strategies agreeing. This corrects Lean's physical-leaf projection; it does not assert an existing peer defect.
- `extent extension`: The same checkpoint now retains 33 documents across five group/keyed forms and three carriers. Empty/omitted leading branches differ from suffixes in every form; unavailable key controls preserve ordinary-group results. Reuse these captures for reconciliation.
- `acceptance`: Reconcile nested first-filled traversal and polarity using the retained observations. Preserve terminal hiding and unavailable-value handling; include the measured ordinary group, starred group and keyed lower-star/group/starred-group controls across String, Number and Boolean. Partial validation and wider profiles remain separately bounded. Introducing revision is the first commit containing this ID; no reviewed peer response yet.

<a id="spec-2026-10-10-15"></a>
### SPEC-2026-10-10-15 — partial value lists accept complete concrete declared-slot coverage

- `status`: pending
- `canonical`: [Partial value-list extent](../spec/10-validation-and-polarity.md#5-full-vs-partial-validation) separates declared-slot coverage from relevant concrete witnesses and the runtime's separate USB gate.
- `delta`: Concrete selectors covering rows one and two establish an ordinary capacity-two extent; the same selectors leave a capacity-three extent unknown even when its third row is absent. Do not require a wildcard at every repeated group or infer completeness from physical rows alone. Preserve the three quantifiers' side-specific UNKNOWN policy.
- `basis`: [Two-capacity Number/String matrix](sources/group-list-and-capacity-probes.md#src-partial-list-declared-extent), 28 documents, field/group operands and both sides, with both strategies agreeing. Maintained reader-to-evaluator readback matches all 672 partial pointer/type comparisons after correcting 54 divergences.
- `acceptance`: Reconcile the wildcard-only account against the retained capacity controls and source; retain distinct count/aggregate gates. Report exact adopted revision or contrary evidence. Nested/keyed, wider profiles and separate USB-host behavior remain explicitly uncalibrated. Introducing revision is the first commit containing this ID.

<a id="spec-2026-10-10-16"></a>
### SPEC-2026-10-10-16 — selected lists cover lower declared slots and retain absent-list omission

- `status`: pending
- `canonical`: [Selected partial coverage](../spec/10-validation-and-polarity.md#5-full-vs-partial-validation) and [absent selected lists](../spec/08-paths-and-references.md#41-what-a-semantic-index-read-yields).
- `delta`: A matched key binds the selected parent; lower declared slots may be covered concretely. No selection requires a wildcard at the parent, but not every lower level. No and values-side NotAll preserve absent-list OMISSION on full and partial validation.
- `basis`: [Two-carrier selected-list matrix](sources/group-list-and-capacity-probes.md#src-selected-list-declared-extent), both strategies agreeing; 552 full and 552 partial exact pointer/type comparisons. This corrects Lean's shared extent/polarity adapters and does not assert a peer defect.
- `acceptance`: Reconcile Number/String lower field/starred-group lists, both sides and all three quantifiers against retained selected, absent and excluded controls. Keep counts/aggregates separate; wider profiles and deeper topology remain uncalibrated. Introducing revision is the first commit containing this ID; no peer response yet.

<a id="spec-2026-10-10-17"></a>
### SPEC-2026-10-10-17 — nested group-count growth uses all reopened capacities

- `status`: pending
- `canonical`: [Count extent and message polarity](../spec/10-validation-and-polarity.md#41-the-same-rule-fires-either-type).
- `delta`: A starred group count's extent is the product of reopened capacities, not just its terminal group's maximum. Bound ancestors and descendants below the operand do not contribute. Full/partial rule polarity and implicit computation messages use the same extent.
- `basis`: [Two-axis matrix](sources/group-count-topology.md#src-nested-group-count), both Kernel 30.8.1 strategies agreeing. Empty prefix/suffix and missing-parent controls count two against extent four; full capacity counts four. This corrects Lean's shared extent projection and does not assert an existing peer defect.
- `acceptance`: Reconcile nested starred and below-star count growth with the retained rules, seeded computation values and implicit messages. Preserve partial first-instance gates and distinguish structural rows from fixed-group content. Report the adopted exact revision or contrary evidence; wider topology remains explicitly uncalibrated. Introducing revision is the first commit containing this ID.
