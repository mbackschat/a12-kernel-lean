# spec/07 rewrite — change notes

Outputs: `07-new.md` (the new chapter) and `14-new07.md` (spec/14 in full, with the new T column). Classification: navigation, structure and provenance cleanup plus the decisions listed below; no rule is dropped.

## Findings

- ch07-1: fixed (§5.2): the "all possible repetitions" bullet became a pointer to spec/02 A.4.2's per-operator range table.
- ch07-2: fixed (§2.2): "same name and type" replaced by "same name, kinds forming an admitted pair", with the measured pair table.
- ch07-3: fixed (§2.3): the join construction moved from the note into rules (token union, normalized lookup, duplicate exclusion, relevance before identity, the three partial consequences); the note keeps only modelling advice.
- ch07-4: fixed (§1.8 leaf table): value comparisons narrowed to the measured stored-DateRange equality and extracted-endpoint rows; the zero-converting `==`/`>=`/`<=` refusal of old 07:41/07:49 stands (cited, not a decision).
- ch07-5: fixed in 07 (§1.1 bounded cases: the address may name a first row with no stored content, which is not the partial-validation phantom row of spec/01 §2.2); the 01:134 sentence is under Other chapters.
- ch07-6: fixed (§2.4): the stale 07:98 limitation deleted; the unmatched side reads as an empty row, its key field included. The Lean docstring caveat is under Other chapters.
- ch07-7: fixed (§3.5 carrier table): the distinct count's Boolean/Confirm refusal is the leading-slot class, as old 07:180 states.
- ch07-8: fixed (§3.3, §4.3): an empty domain yields the consuming operator's all-empty identity, not a definite `0`.
- ch07-9: fixed (§4.3): the over-capacity-only document answers with the in-capacity projection's all-empty first-filled identity.
- ch07-10: fixed (§3.5): `MVK_VARYING_TYPES_NOT_ALLOWED` for a sole heterogeneous group is named as `FirstFilledValue`'s carrier, beside `Sum`'s and `MaxValue`'s classes.
- ch07-11: fixed (§2.1 frames table): common frame and one-sided frame stated separately; diverging frames "not stated". Behavioural decision 1.
- ch07-12: fixed (§1.1): "evaluates exactly once" became "at most once", the content gate of spec/03 §A.4 and root dispatch deciding whether it runs.
- ch07-13: fixed (§1.3 domain and consumer tables, §3.9 scans) and the new spec/14 column T with its `### Traversal` section; the rule iteration domain (threshold 5) and filter occupancy (threshold 100) stay distinct.
- ch07-14: fixed (§1.8): one leaf-class table with an evidence column (measured vs source) replaces the scattered statements; `MaxValue` and `SumOfProducts` zero sensitivity marked source.
- ch07-15: fixed (§2.4): one instance-view rule plus bounded deviations replaces the leaf-by-leaf enumeration.
- ch07-16: fixed (§3.5): one carrier-by-gate table (kind domain, leading slot or whole list, class), the long paragraph split.
- ch07-17: fixed (§3.6): one value-identity table per operator and kind family.
- ch07-18: fixed (§2.2): the cross-kind pairs' runtime match identity is stated as unmeasured beyond admission.
- ch07-19: fixed (§3.9): a filter executes at a missing coordinate of the traversal extent while the coordinate never enters an instantiated-range tally (old 07:202 decides it).
- ch07-21: fixed (§4.3): nested-star over-capacity exclusion kept as a measured-only scope (targets measured, operands unmeasured).
- ch07-22: fixed (§5.3): the compared set is bounded by the operand's depth: levels above and at an unstarred operand stay bound, levels below reopen. Behavioural decision 2.
- ch07-23: deferred: the document JSON conversion stays in §1.2 until spec/01 §2 receives it (Other chapters).
- ch07-24: deferred: the error-target declaration stays in §1.6 until spec/01 §3.1 receives it (Other chapters).
- ch07-25: partially fixed (§1.10): the kind-based sub-day sentence is replaced by the format rule (Minutes/Seconds marked unmeasured), and the runtime facts are fenced as a list stated to be owned by 04/05/06; they still sit in 07, because the move needs those chapters' rewrites (Other chapters).
- ch07-26: fixed: §1.3 links spec/03 §A.4 for the content gate; old 07:300–302 merged into §3.9 and §5.3; the empty-line run removed; old 07:204 links spec/09 §3.3. Old 07:194 (filter walk against a key) is kept in §3.1 because no spec/08 sentence holds it yet (Other chapters).
- xc-3: fixed (§1.1 bounded cases): unbound error-path levels pin to coordinate 1 unless spec/08 §4.3 reanchoring applies.
- ch01-2: fixed (§1.4): one reference-set contributor table (direct, group expansion, `@From`, `$`-marked `Having` reads; unmarked filter reads refused).
- ch01-18: not applicable in 07: §1.6 names the error-target classes; spec/01 should link them.
- ch02-2: not applicable in 07: the `FieldFilled` over malformed computation case is kept in §3; the poison split is spec/02's.
- ch02-4: not applicable in 07 beyond adding the anchor `#negative-condition-guard` (§1.8) that spec/02:62 should link.
- ch02-12: fixed (§4.3): "each node the document writes at or beneath the row".
- ch02-14: not applicable: spec/02 keeps B.3; §4.3 still names spec/02 as owner.
- ch03-12: fixed (§3.5): `FirstFilledValue` operand admission and expansion moved in from spec/03:77.
- ch03-14: fixed (§1.1): the first-row anchor is tied to the content gate exactly as spec/03 §A.4 states it (repeatable root skips the gate; nonrepeatable keeps it); cited, not a decision.
- ch04-2: not applicable in 07: §1.8 already carries the iteration precondition for the converted-zero refusal; spec/04 should cross-reference it.
- ch04-18: fixed (§3.4): the aggregate operand grammar (field paths only) is stated here, with spec/04 under Other chapters.
- ch05-1: fixed in 07 (§1.10): sub-day differences gate on the declared format, not the kind; the spec/05 §9 half is under Other chapters.
- ch05-13: not applicable in 07: the per-unit admission table belongs to spec/05; §1.10 keeps only the scope contribution and year agreement.
- ch06-17: fixed (§4.2): "open declared tail" is the defined term; spec/06's "omitted tail" is under Other chapters.
- ch08-1: not applicable in 07 beyond §2.3 using "compromised" as spec/08 §4.1 should define it (Other chapters).
- ch08-2: not applicable in 07: the eligibility rule moved from the note into §2.3 rules; spec/08 §4.3 should state it (Other chapters).
- ch09-2: not applicable: §3.3 states the empty-domain identity by result family, which spec/09 now cites.
- ch09-24: pointer fix only (§3.1): the constant-ladder pointer now targets spec/09 §1.4; the ownership move to the comparison chapter is spec/05's or spec/09's (Other chapters).
- ch10-2: not applicable: the classification leaf table is spec/10's and spec/14 column E's.
- ch10-9: not applicable: 07 states only `CurrentRepetition`'s guard class.
- ch10-10: fixed (§1.7): the group-target partial-validation sentence became a pointer to spec/10 §5.2 item 3.
- ch12-1: not applicable: §1.9 keeps the measured 19-digit literal.
- ch12-17: not applicable: 07 keeps star legality; spec/12 should point to it.
- map-6: fixed (§1.1): "phantom first-row anchor" removed; "phantom row" is used only for spec/01 §2.2's partial-validation notion.
- feedback spec/07 §1 L9 (Q-002, unfit document shapes): fixed (§1.2): stated as "not stated".
- feedback spec/07 L61 (§2, keyed side under an unkeyed outer level): fixed (§2.1 one-sided frame row).
- feedback spec/07 L182 (`SumOfProducts` empty-factor polarity): §3.8 keeps the old rule (an empty cell supplies zero with its own declaration's directional missingness); an earlier draft's pointer to a spec/10 §4 per-pair row was removed because no such row exists. spec/14's `pair product` class now links 07 §3.8.
- 10-notes move of spec/04:136–143 capacity and over-repetition bullets (ch04-10/xc-5 remedy): fixed (§4.3, new `NumberOfValueInFields` bullet: computation group carriers, full-validation starred String/Boolean/Confirm extents, the reflexive-filter scope, and structural findings beside each result; checkpoint `src-filtered-starred-field-capacity` added to Sources). The filter-polarity part of those bullets belongs to spec/10 §4 and is not moved here; spec/04 deletes the moved bullets (Other chapters).
- Lean check of `FieldsNotCollectivelyFilled`'s validation scan: resolved, no conflict. `evaluateFilteredFill` in `A12Kernel/Elaboration/FieldFillList.lean` runs its first stage as `scan .atLeastOneFieldFilled`, which `scanValidationFill` traverses `.sparse`, then `scan .notAllFieldsFilled` over declared environments; this matches §3.9 and spec/14 T `sparse-enabled then declared`.
- feedback spec/07 §3 L110–229 (which consumers are sparse): fixed (§3.9 class definitions, spec/14 column T).
- feedback spec/09 §5 → spec/07 §2 (computation partner joins): fixed (§2.3 pointer to spec/09 §5.4).

## Behavioural decisions

1. **Parallel frames (ch07-11).** Old 07:78: "a repeatable **non-indexed frame** is legal above exactly one joined group." Old 07:90: "A common outer repetition binds both sides before their key union is constructed, so equal keys in different outer rows do not join." Taken: both hold, as two frame classes (§2.1); diverging frames are "not stated". Lean: `ParallelOuterScopePlan.classify` and `admitsErrorOnLeft` in `A12Kernel/Elaboration/CheckedIndexColumn.lean` (common vs one-sided; no plan for diverging). The one-sided row is measured (checkpoint `src-partial-parallel`, `frames` row); the common-frame sentence is the old text's.
2. **Group-operand compared set (ch07-22).** Old 07:287: "A rule authored on a repeatable group whose operand names an ancestor compares that ancestor's whole extent". Old 07:243: "ancestor-or-self, per row, judging the *current* row's cells." Taken: levels above and at an unstarred operand stay bound at the rule's binding, levels below are reopened (§5.3); the bare repeatable operand case is marked unmeasured. Lean: `CheckedEntityGroupSource.boundLevelCount` in `A12Kernel/Elaboration/FieldEntityList.lean` (operand scope length when fixed, `firstStar` when starred); LF92.

Decided by an existing sentence, cited rather than decided here:

- Sub-day differences gate on the declared format (ch05-1): old 07:55 "accept DateTime fields only, require the selected time component and compatible year presence" against spec/05:68 "the declared format's component set decides this gate, and the declared kind takes no part"; measured at checkpoint `src-temporal-difference-gates-read-the-format`; Lean `DateTimeSubdayUnit.admittedBy` in `A12Kernel/Semantics/DateTimeDifference.lean` agrees.
- Value comparisons in the guard (ch07-4): old 07:272 "outside the gate at every polarity" against old 07:41/07:49's zero-converting refusal; 07:49 decides.
- Once-rule content gate (ch03-14, ch07-12): spec/03 §A.4 decides; Lean `evalOrdinaryOnceFull` in `A12Kernel/Elaboration/ValidationRule/Execution.lean` agrees.
- Empty-domain identity (ch07-8), first-filled over capacity (ch07-9), leading slot (ch07-7), `FirstFilledValue` heterogeneous group (ch07-10), unmatched key read (ch07-6), filter at missing coordinates (ch07-19): decided by old 07:144/07:172, 07:172, 07:180, 07:152, 07:76 and 07:202 respectively.
- Reanchoring (xc-3): spec/08 §4.3 decides; Lean `reanchorSelectedError` agrees.

Unmeasured extensions marked in the text:

- Sub-day format rule for `DifferenceInMinutes` and `DifferenceInSeconds` (§1.10): the checkpoint measures `DifferenceInHours` only; Lean `DateTimeSubdayUnit.admittedBy` in `A12Kernel/Semantics/DateTimeDifference.lean` applies the same format rule to all three units. Marked unmeasured.
- Common-frame outer rows follow the rule iteration domain (§2.1): only one-sided frames are measured (`src-partial-parallel`, `frames` row). Lean `ParallelOuterScopePlan.common` admits the common frame; the outer-row enumeration was not traced to a def. Marked unmeasured.
- Group-list leaf guard classes (§1.8 table): old 07:47 gave no evidence mark; now "stated without measurement".
- Semantic-index contributor row (§1.4) and the payload-guard bullet (§1.5): Kernel source reading (old 07:24 "source-grounded", `src-having-reference-scope`); marked unmeasured.
- Mixed vs all-iterating semantic-index distinction (§1.8): Kernel source reading and retained `Sum` disjunctions; other carriers marked unmeasured (old 07:43).

## Unresolved

- Lean `FieldKind.joinsAsIndex` admits only equal kinds or two Numbers, narrower than the measured cross-kind pairs of §2.2. Spec kept; Lean gap.
- spec/05 §9 still states the sub-day and extraction gates by kind (ch05-1's spec/05 half).
- Whether Confirm or DATE_RANGE behind an admitted leading operand of `NumberOfDifferentValues` draws the leading-slot class or another is unmeasured; §3.5 says so.
- `SumOfProducts`' traversal range is not stated (spec/14 T "not stated; filter n/a").

## Rules not kept

None. The root-group cascade's "its classes are reachable from nowhere else" (old 07:26, no measurement cited) is now "no witness is known of another route drawing its classes". Dropped commentary only: "the gate's reach is presence-shaped rather than polarity-shaped", "a consumer must ask rather than predict it" (reader advice on `MVK_NEG_CONDITION_IN_ITERATION`), the `FieldValuesNotUnique` "observed contract, not derivable from star machinery" warning, the withdrawn peer `{DateRange}` category narrative, and the "earlier version" and "rival account" narratives; each rule they surrounded is kept.

## Other chapters

- spec/01 §2: take the document JSON conversion from 07 §1.2 (ch07-23); then 07 §1.2 becomes a pointer.
- spec/01 §3.1: take the error-target declaration from 07 §1.6 (ch07-24) and name its classes where 01:144 says "the error-target pair" (ch01-18).
- spec/01:134 and §2.2: limit "only partial validation names a row that does not physically exist" to rule messages over physical rows, since full validation fires at declared slots (ch07-5, map-6).
- spec/01:151: replace the reference rule with a pointer to 07 §1.4 (ch01-2).
- spec/02:62: say "unguarded" and link `07-repetition-and-iteration.md#negative-condition-guard` (ch02-4).
- spec/03:77: delete the `FirstFilledValue` admission and expansion now in 07 §3.5 (ch03-12).
- spec/04:52: replace the aggregate operand grammar with a pointer to 07 §3.4 (ch04-18); spec/04:124 cross-reference the iteration precondition of 07 §1.8 (ch04-2); take the `RangeAsNumber` and `FieldValueAsNumber` runtime bullets of 07 §1.10.
- spec/05 §9: delete the kind-based extractor and sub-day statements (ch05-1); add the per-unit admission table (ch05-13); take the temporal-extraction and difference runtime bullets of 07 §1.10 (ch07-25).
- spec/06: take the `Length` runtime bullet of 07 §1.10 (ch07-25); rename "omitted tail" to "open declared tail" (ch06-17); 06:152 may point to `14-operator-reference.md#traversal`.
- spec/08 §4.1: define "compromised" index (ch08-1); §4.3: state the selection eligibility rule now in 07 §2.3 (ch08-2); take the filter-walk-against-a-key paragraph of 07 §3.1 (ch07-26).
- spec/12:122: point to 07 §4 and spec/08 for star legality (ch12-17).
- spec/04:136–143: delete the capacity and over-repetition bullets now in 07 §4.3; their filter-polarity sentences go to spec/10 §4.
- spec/14 F and X for temporal operand-list `Min`/`Max` read "not stated" while 07 §3.5 states that `Min`/`Max` refuse a starred field and a group operand; those cells could become `n/a` under the F basis (T is already `n/a`).
- spec/14: replace with `14-new07.md` (column T, `### Traversal`, row-drop/key-fillability/pair-product links narrowed to 07 §6.2, §6.3, §3.8).
- Lean docstring of `keyOnlyEnvironment?` carries the stale caveat deleted in ch07-6.
- docs/IMPLEMENTATION-MAP.md: name the Lean owners of the T classes (`StarPath.boundedFilterEnvironments`, `FilterTraversalMode`, `RuleIterationDomain`, `repetitionKeyRowEnvironments`).
- Possible future spec/14 columns (guard class, group-operand admission) stay chapter tables in 07 §1.8 and §3.5 for now, per the ch07-14 and ch07-16 remedies.

## Anchors

- `#1-when-a-rule-iterates-and-where-its-error-lands`: unchanged heading, §1.
- `#2-parallel-iteration--joining-two-repeatable-groups-by-key`: unchanged heading, §2.
- `#3-the-filter-having-the--correlation-and-aggregation`: unchanged heading, §3.
- `#4-where-a-star-binds--the-anchor-rules-`: unchanged heading, §4.
- `#5-groupfilled-and-the-other-repetition-rules`: unchanged heading, §5.
- `#6-repetitionnotunique-precisely-`: unchanged heading, §6.
- `#entity-list-operand-reads`: explicit `<a id>` now at the head of §3.5.
- `#checklist-for-9`: unchanged heading.
- New: `#negative-condition-guard` (§1.8, for spec/02:62), numbered subsection anchors such as `#13-evaluation-domains`, `#39-filter-traversal`, `#62-the-duplicate-relation`, and `14-operator-reference.md#traversal` (in `14-new07.md`).
- Checked: every link in `07-new.md` and `14-new07.md` resolves against the spec tree with the two new files substituted (0 missing).

## HIGH review (2026-10-26)

- Preservation check: 501 old statements; 473 kept, 9 generalised safely, 13 declared changes; it found 2 lost scope limits (the semantic-index carrier calibration bound and the two-level one-star bound) and 4 altered statements (the semantic-index contributor evidence mark, the non-constant comparison side, the first-star locus and a widened key-list precedence). All six are restored in the installed text, together with four unmeasured marks (sub-day Minutes and Seconds, the common-frame outer rows, the group-list guard row and the `SumOfProducts` pointer).
- Both behavioural decisions were checked against Lean and carried as SPEC-2026-10-26-13 (frames) and SPEC-2026-10-26-14 (compared set by operand depth); the -14 delta restates the old texts as two cases of one rule rather than a replacement.
- Unresolved item one, Lean's equal-kind index join, is recorded as a representation boundary under SG9; the others stay owed to spec/05 and later chapters.
- The spec/04 capacity bullets now duplicated in §4.3 stay in spec/04 until its rewrite deletes them, as Other chapters records.
- spec/10's product extent pointer now targets §3.8. The Lean docstring that still names spec/07 §4 for keyed products is left for the cross-chapter pass.
