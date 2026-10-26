# spec/05 rewrite — change notes

## Findings

- ch05-1: fixed (§9 rewritten: the kind-based extractor and sub-day statements are deleted and replaced by the component classes of §9.2; `AddDays` time preservation moved to §2.1, the `DifferenceInDays` stepping and its examples to §2.5).
- ch05-2: fixed (§9.2, clock-only DATE_TIME paragraph): split extractors need a date and a time half, sub-day operations need a date half, numeric clock extractors need only their letter; `HoursFromTime` on that carrier is measured (`src-cross-kind-temporal-reads`, `src-cross-kind-computation-reads`), `MinutesFromTime` and `SecondsFromTime` are marked unmeasured.
- ch05-3: fixed (§1 "The omitted-year constant and the Base Year"): an all-yearless operation without a Base Year is scoped to units that do not need the year; year-unit operations and year extraction need a year component or a declared Base Year (§9.2 `part y`, `step y`).
- ch05-4: fixed (§6.2 cause order; §4.2 message keys): omission pattern before reality, witness `YEAR_OPTIONAL` `0000-13-00`; measured by the K22 message-key capture. Behavioural decision 1.
- ch05-5: fixed (declared-formats section "The format vocabulary"): the thirteen-string allowlist stated once with the six year-free members; §4.1 and the checklist use thirteen; the measured stored-text classification scope is stated there.
- ch05-6: fixed (checklist): sub-day differences use epoch milliseconds.
- ch05-7: fixed (§2.7, §3.4): the Julian-reality examples use field components; quoted-constant years stay bounded by §1.
- ch05-8: fixed (§6.2): the "merely selects a cell" rationale is deleted; the field-list split is stated as a measured rule, and `FirstFilledValue`'s earliest-day selection stays beside it.
- ch05-9: fixed (declared-formats section "Where a yearless value gets its year"): one carrier table; "2000 wherever observable" is not carried across carriers.
- ch05-11: fixed (§4.1): the year co-requirement is scoped to DATE and DATE_FRAGMENT, DATE_RANGE exempt.
- ch05-12: fixed (§1 "Cross-kind comparison classes"): the `==` arm order, scoped to an equality between two fields with arms 1–2 claiming only Confirm and Boolean fields (so `[Window] == True` keeps its measured `MVK_INVALID_COMPARE_TO_DATE_RANGE`), and the two-step ordering rule with the orderable kind set. Behavioural decision 6.
- ch05-13: fixed (§9.2 component classes and step ladder; spec/14 column D in 14-new05.md). Behavioural decisions 2 and 3.
- ch05-14: fixed (§3.7, §6.2, §8.4): the spec/08 §3 read ladder is linked and the per-carrier lists are labelled measured per carrier.
- ch05-15: fixed (§6.2 precision classes; spec/14 column D precision half, unmeasured cells marked in its measured-scope sentence).
- ch05-16: fixed (§5 "The nonexistent wall label"): one carrier table; unmeasured carriers are "not stated".
- ch05-17: fixed (§2.1): every numeric extraction and every difference is non-expandable scale-0; the day and sub-day units are marked unmeasured. Behavioural decision 4.
- ch05-18: fixed as "not stated" (§2.7): the calendar of stored-source shift chains landing before the cutover is not stated; the side claim that a stored source lies on or after the floor is dropped (false for a stored `MM` value under a Base Year below 1583). Listed under Unresolved.
- ch05-19: fixed (§2.3, §9.2 rung 6): `AddMonths`/`AddYears` refuse a time half with `MVK_WRONG_DATE_FORMAT_FOR_OP`, measured.
- ch05-20: fixed (§2.1, §9.1): a shift's result carries its source's component set, unmeasured for non-default sources. Behavioural decision 5.
- ch05-21: fixed as unmeasured (§8.5): two spellings of one format string in one reference are admitted and `MM-dd` with `dd.MM` refused, both marked unmeasured; Lean does not settle it. Listed under Unresolved.
- ch05-22: fixed (§1 clock-constant bullet; §8.1): the Time-target class is the constant ladder's temporal rung `MVK_INVALID_COMPARE_TO_DATE`, the measured row recording only the refusal; an odd-length empty-separator token is `datumBereichFormatFalsch`, unmeasured. Behavioural decision 7.
- ch05-23: fixed (§2.6): the strategy-split sentence is deleted and its limit kept as scope: measured on the Groovy-dynamic strategy with static Java agreeing, no identical-behaviour claim for a TypeScript/luxon target; Kernel source links are replaced by prose rules with `Sources:` lines.
- Coordinator preservation check (2026-10-26): arm scoping (ch05-12), DateTime argument order (decision 3), ch05-21 basis, `HoursFromTime` scope, ch05-18 side claim, TypeScript scope, validation-only UNKNOWN in §2.8, rung order and `date + clock` scope, spec/14 D scope, the §5 parse wording, the `datumFalsch` definition, exclusivity phrasing, the `c4864f70e` pin, ten duplicates and the listed narrative are fixed; each subsection keeps its own `Sources:` line, the Berlin profile's full a12-dmkits test description included.
- ch05-25: deferred (the move into spec/04 needs the spec/04 rewrite; §1 keeps the constant-pair gate and arm order until then; under Other chapters).
- ch05-26: fixed (new section "Declared formats and stored temporal text" gathers the format model; the 05:68/05:160 extractor gate is stated once in §9.2).
- xc-6: fixed (§2.1): an empty Date operand of an extraction or difference is the fillable `0` in both phases, measured; spec/09's DATE column is already limited by the spec/09 rewrite.
- ch01-13: fixed within spec/05 (§5): the legal zone-id set is a host input, a versioned legacy id table; the spec/01 half is under Other chapters.
- ch04-9: deferred (spec/04 owns the merged gate; under Other chapters).
- ch04-15: fixed (§2.1): "non-expandable" is defined once and linked to spec/04 §1's multiplicative-constant capability.
- ch06-15: fixed (§3.7 owns the whole named-type predicate, the runtime-failure route for an unregistered name included); spec/06 A.3's pointer under Other chapters.
- ch07-25: fixed (§2.8): the temporal extraction and difference runtime bullets of spec/07 §1.10 are taken; the spec/07 deletion is under Other chapters.
- ch09-6: not applicable (the Base-Year field-copy question is spec/09's; spec/05 decides only the comparison gate's Base-Year exemption, §1).
- ch12-5: not applicable within spec/05 (slot classes are spec/14 column S; spec/05 names no slot list).
- ch12-6: fixed (§1 omitted-year constant: completion uses the Base Year or the leap default whenever a year is needed; the Base Year is required only when years disagree).
- ch12-7: fixed (§1 classification table: shape, real hybrid-calendar date, ASCII digits, zero padding, value-list exception).
- ch12-15: fixed (§1 takes the zero-padding, omitted-year negatives and date-time spelling facts from spec/12 §2; spec/12 §2 pointer under Other chapters).
- map-1: not applicable within spec/05 (SEMANTICS-MAP edit; under Other chapters).
- map-2: not applicable within spec/05 (SEMANTICS-MAP edit; under Other chapters).
- Q-006: fixed (§6.2 step 3 and §4.2): the spec decides omission before reality.
- Q-009: fixed (§3.7): an unregistered name aborts the rule through the runtime-failure route and yields one VALUE message; not a true leaf.
- Q-015: fixed (§6.2 extractor bullet): an admitted extractor reads a stored component every value of its precision carries; no completion is involved.
- 07-notes request (§9 kind-based statements, admission table, runtime bullets): fixed as ch05-1, ch05-13, ch07-25.
- 09-notes request ch05-13 (operand-gate table): fixed (§9.2 and spec/14 column D); spec/09 §4.1's pointer under Other chapters.
- 09-notes request ch05-16 (zone-label table): fixed (§5), the computed-target row pointing to spec/09 §4.1.
- 09-notes request ch09-24 (constant ladder and field-pair walk of spec/09 §1.4): not applicable here; spec/04, the comparison owner, is the right owner (Other chapters). spec/05 keeps only the temporal arms and the temporal pair gate.
- 10-notes request (a constructed-`Date(...)` `Valid`/`Invalid` refuses a condition without an immediate field component): confirmed, kept in §3.6 (`MVK_ONLY_CONSTANTS_USED`, measured).
- 12-notes request (relabel 05:111's spec/12 link): fixed (§3.2 links concrete syntax §3.1 `#31-which-class-a-refused-text-draws`).
- 12-notes request (take the spec/12 §2 shape facts): fixed as ch12-15.
- 14-notes request (move membership facts out of spec/05 and point to spec/14): fixed for the overlap predicates' V/P/F classes, the date-validity P class and the shifts' `not-given` (§3, §8 state mechanisms; the preamble points to spec/14).

## Behavioural decisions

1. Partial-Date cause order (ch05-4, Q-006). Old 05:191: "A partially known Date first meets its omission check, whose keys carry the code `datumFalsch`". Old 05:309: "test the present components' reality *before* their position in time, and both before the precision gate". Side taken: omission pattern before reality. Lean is split: `dateMessageKey?` and `TemporalPartialMode.omissionMessageKey?` in `A12Kernel/Semantics/DateFormalMessageKey.lean` put omission first; `classifyPartialDateStored` in `A12Kernel/Semantics/PartialDateInput.lean` runs reality first for omitted-day shapes. The K22 message-key capture row d5-3 (`0000-13-00`, `YEAR_OPTIONAL`) measures `datumFalsch`, so the measured side is stated and the classifier is a Lean defect (Other chapters).
2. Step ladder (ch05-13). Old text: none; the per-unit codes were stated only by example (05:70, 05:160, 05:410). Side taken: precision, non-temporal, unit component (Base Year supplies the year), date half, no time half for months and years, year agreement for a difference. Lean: `checkRawTemporalArithmetic` in `A12Kernel/Reference/Dm/HavingTemporalAdmission.lean`, `DateDifferenceUnit.admittedBy`/`operandFault?` in `A12Kernel/Semantics/DateDifference.lean`, `TemporalOperationUnit.operandFault?` in `A12Kernel/Semantics/TemporalFormat.lean`. Rungs 1, 4 before 5 under a Base Year, 4 before 7 (`granularity-precedes-agreement` in `src-yearless-anchor-is-the-base-year`) and 7 with its Base-Year removal are measured; rungs 2–3 are marked unmeasured.
3. `DateTime(date, time)` argument gate and partial refusals (ch05-13, ch05-15). Old text: silent. Side taken: `date + clock` class, its component sets and yearless-source Base-Year requirement measured in `src-value-as-date-locus`'s 2026-10-04 composition table; shifts and differences refuse a direct partial field `MVK_INVALID_DATE_TYPE` ahead of their component gates (`checkRawTemporalArithmetic` in `A12Kernel/Reference/Dm/HavingTemporalAdmission.lean`), while the `DateTime` Date argument runs its component and year check first and the partial check after (`rawDateTimeConstructorType` in `A12Kernel/Reference/Dm/HavingConstructorAdmission.lean`). Both partial orders marked unmeasured.
4. Day and sub-day differences non-expandable scale-0 (ch05-17). Old 05:68: "plus date-formatted `DifferenceInMonths`/`DifferenceInYears`, each produces a non-expandable scale-0 Number operation". Old 05:95/§9: day and sub-day units silent. Side taken: all six difference units. Lean: `ResolvedNumericAtom.summaryWith` in `A12Kernel/Elaboration/NumericSource.lean` (day and sub-day differences are `NumericScaleSummary.field 0`). Marked unmeasured.
5. Shift result component set (ch05-20). Old 05:160: "derived temporal operands `AddDays`, `AddHours` … each admit exactly the extractors their kind's default format carries". Old 05:410: "`AddDays` accepts a DateTime operand and is TIME-PRESERVING". Side taken: a shift carries its source's set. Lean: `rawTemporalShiftType` in `A12Kernel/Reference/Dm/HavingTemporalAdmission.lean`. The two agree on every default-format source; the non-default case is marked unmeasured. Supporting observation: the yearless-anchor checkpoint records `YearFromDate(AddDays(<yearless constant>, …))` refused `MVK_WRONG_DATE_FORMAT_FOR_OP`, which the kind-default reading would admit. `StartOfDateRange` is decided by §8.3's measured endpoint rule instead (already in the chapter).
6. Ordering comparison classes (ch05-12). Old 05:54: "`==` arm order" only; ordering silent. Side taken: orderability gate first (Number and temporal kinds orderable), then temporal against Number. Lean: `orderingComparisonDiagnostic?` in `A12Kernel/Elaboration/LiteralComparisonDiagnostic.lean`, `SurfaceScalarKind.orderable` in `A12Kernel/Elaboration/ComparisonEntry.lean`. The rule is stated with its measured members (§1); the general two-step order beyond them is Lean's.
7. Odd-length empty-separator range token (ch05-22). Old text: midpoint split, odd length silent. Side taken: `datumBereichFormatFalsch`. Lean: `halveDateRange` in `A12Kernel/Elaboration/DateRangeInput.lean`. Marked unmeasured.
8. Precision classes of the extractors (ch05-15). Old 05:160 and 05:165 agree; cells taken from them and `admittedPartialMode` in `A12Kernel/Semantics/DateNumeric.lean`. Measured.
9. Unregistered named type (Q-009, ch06-15). Old 05:169: "both predicates fire for a filled field, each as an ordinary rule message carrying VALUE polarity at the concrete error address". spec/06 A.3 (already decides): the registry lookup failure is a runtime failure. Side taken: spec/06 A.3, cited; Lean `A12Kernel/Semantics/CustomFieldValidity.lean` agrees.

## Unresolved

- ch05-18: the calendar basis of shift chains from stored sources landing before the 1582 cutover is written "not stated" (§2.7); Lean uses a stored-Gregorian basis without a measurement.
- ch05-21: whether one overlap reference expanding to two spellings of one format string (`MM` with slash and with the empty separator) is admitted, and `MM-dd` with `dd.MM` refused. Old 05:370 reduces each reference to "distinct format spellings" and is silent on this case; Lean's `dateRangeFormatAgreement` (`A12Kernel/Semantics/DateRangeOverlapOperators.lean`) has no production caller, so Lean does not settle it. Kept in §8.5 marked unmeasured.

## Rules not kept

## Other chapters

- spec/04 §1 (ch04-9, ch05-25, ch09-24): take the brace-preserved constantness and the `Today`/`Now` exemptions of the constant-pair gate, the cross-kind `==` arm order and two-step ordering rule, and spec/09 §1.4's constant-assignment ladder and field-pair comparison walk; spec/05 §1 then keeps only the temporal arms and the temporal pair gate, pointing to spec/04.
- spec/06 A.3 (ch06-15): replace the `Valid`/`Invalid(Field, "Name")` runtime content with a pointer to spec/05 §3.7, but keep the factory/registry lookup sentence there (it governs declared-field validation); spec/05 §3.7 points to it.
- spec/12 §2 (ch12-7, ch12-15): replace the date-shape rows (zero padding, omitted-year negatives, date-time spelling) with a pointer to spec/05 §1, and delete as duplicates of spec/05 §1 the clock row, the value-list sentence in the String row and the paragraph after the table (a quoted literal failing the temporal shapes is a String).
- spec/07 §1.10 (ch07-25, ch05-1): drop the temporal extraction and difference runtime bullets and point to spec/05 §2.8 and §9; at line 281 change "DifferenceInMinutes/Seconds format rule unmeasured" to measured at the date-time and clock formats (spec/05 §9.2 measured scope).
- spec/09 §4.1 (ch05-13): the operand-gate sentence points to spec/05 §9 and spec/14 column D.
- spec/01 (ch01-13): the legal zone-id set is the host input spec/05 §5 names; spec/01's JDK-call definition becomes a pointer.
- spec/14: replace with 14-new05.md (column D, its vocabulary section, checklist line).
- spec/SEMANTICS-MAP.md (map-1): DateFragment row says "any date-bearing format" and links spec/05 §6.
- spec/SEMANTICS-MAP.md (map-2): DateRange row says "declared separator (eight admitted pairs)" and links spec/05 §8.
- Lean (docs, not spec): `classifyPartialDateStored` diverges from the measured K22 row d5-3; docstrings describing the derived-operand kind default should follow behavioural decision 5.
- Ledger: decisions 2–7 change or extend spec/05 behaviourally and need SPEC- classification in docs/A12-DMKITS-SPEC-SYNC-LEDGER.md when the rewrite lands, as does the ch05-21 rule kept unmeasured; decisions 1, 8 and 9 restate measured or already-decided rules.

## Anchors

- `#3-constructing-dates-and-checking-validity`: `## 3. Constructing dates, and checking validity`, unchanged.
- `#8-date-ranges-and-overlap`: `## 8. Date ranges and overlap`, unchanged.
- `#1-constant-format-and-the-stringdate-literal-ambiguity-`: `## 1. Constant format and the string/date literal ambiguity ⚠`, unchanged.
- `#2-addition-and-difference-are-asymmetric-and-calendar-corrected`: `## 2. …`, unchanged.
- `#6-date-fragments-and-fragment-ranges`: `## 6. Date fragments and fragment ranges`, unchanged.
- `#4-the-gregorian-floor`: `## 4. The Gregorian floor`, unchanged.
- `#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-`: `## 9. …`, unchanged heading, new content (component classes).
- `#7-the-point-in-time-and-reference-sources`: `## 7. …`, unchanged.
- `#5-time-zones-and-the-sub-day-difference`: `## 5. …`, unchanged.
- `#comparison-entry-and-grouping`: `### Comparison entry and grouping` under §1, unchanged.
- `#temporal-extractor-operands`: explicit `<a id>` in §3.3.
- `#51-versioned-europeberlin-legacy-profile`: `### 5.1 Versioned \`Europe/Berlin\` legacy profile`, unchanged.
- New anchors used by 14-new05.md: `#92-the-component-classes`, `#62-partially-known-dates`, `#the-temporal-pair-gate`, `#31-date`, `#83-bound-extraction`, `#84-construction-and-equality`, `#85-overlap-admission`, `#37-valid-and-invalid-over-a-named-type`.

## HIGH review (2026-10-26)

- Preservation check: 386 old statements; 357 kept, 14 generalised, 14 declared changes, none lost and one altered (the Boolean comparison arms read a constant as a field and contradicted the measured DATE_RANGE class), now scoped to field operands. Lean contradicted two notes: the `DateTime` Date argument checks components before the partial refusal, and the range-separator agreement has no production caller; both are corrected. Several measured rows had been labelled unmeasured and are relabelled.
- After the check the drafter shortened the chapter to a size target, merging Sources lines and cutting explanatory sentences. The Sources lines are restored per subsection, and every cut sentence that was a scope limit, a trap marker or a deciding consequence is restored; the cuts that remain are rationale only, reviewed sentence by sentence against the drafter's removal list.
- The partial-Date cause order is the measured omission-first order; Lean's stored classifier runs reality first and is recorded under SG6.
- Behavioural changes ship as SPEC-2026-10-26-20 (cause order), -21 (temporal operand gate) and -22 (unregistered named type). spec/04, spec/06, spec/07 §1.10 and spec/12 §2 owe the deletions and corrections listed under Other chapters.
