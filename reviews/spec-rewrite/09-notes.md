# spec/09 rewrite notes

Old line numbers refer to `spec/09-computations.md` at `ee761479`. New section numbers refer to `09-new.md`.

## Findings

- ch09-1: fixed (§5.4). One truncated-prefix skip rule with a three-row table; "every instance" survives only as the case where the target scope and the bad group's parent share no repeatable level; the instances are called "skipped", not "marked", so they are not confused with §3.2's invalid-target membership; checklist updated. See behavioural decision 1.
- ch09-2: fixed (§3.2, "A filtered aggregate whose candidates all drop…"). Stated by result family through spec/07 §3 and spec/03 §A.3; the no-value case is scoped to the measured `FirstFilledValue` String row. See behavioural decision 3.
- ch09-3: fixed (§2). Five evaluation outcomes (value, clean no value, poison, domain failure, rejected attempt) with their dependent read and their change projection; VALUE/CLEARED/ERRORED is named the projection in the intro, §2 and §3.3; "CLEARED" in rules that mean the evaluation outcome became "clean no value" or "poison".
- ch09-4: fixed (§5.2). The self-read classes, the containment test and the alternative walk are one section; §1 and §1.2 point to it.
- ch09-5: fixed (§5.3, "The empty-precondition gate is per declaration"). See behavioural decision 9.
- ch09-6: fixed (§4 lead bullets). See behavioural decision 5.
- ch09-7: fixed in part (§1.3 per-alternative scale gate with the band exemption; §6 "errors" qualified as not recorded). See behavioural decision 6 and Unresolved 1.
- ch09-8: fixed (§5.1 walk table; the old 09:246 restatement removed and pointed at the table). See behavioural decision 7.
- ch09-10: fixed (§4.1). The three grounds (family, year agreement, calendar reality) are listed together.
- ch09-11: fixed (§4.1 "The literal must lex as a temporal constant"). Limited to spellings that lex as String or Number, with the measured three targets named.
- ch09-12: fixed (§1.2). One staged table plus bounded cases; the Number-only per-alternative interleaving is labelled; the undecided pairs (containment vs unresolved name, position of the §1.4 wrong-kind classes) are stated as not stated.
- ch09-13: fixed (§5.1). The operand-level walk is stated once as a table; old 09:209 and 09:246 restatements are folded into it.
- ch09-14: fixed (§5.5). One placement-and-scan rule for sibling-star `FirstFilledValue` with a per-kind table (Number, Time, FULL Date, DateTime).
- ch09-15: fixed (§5.5). One `Time(...)` construction rule with a component-form table; component lists are labelled measured scope.
- ch09-16: fixed (§4.1). One temporal-constant gate; old 09:20's temporal half and old 09:164–166 are merged; format rows are examples.
- ch09-17: fixed as declared gap (§4.2 DATE_RANGE last bullet): no rule is stated beyond the declaration-order discriminator and an implementation's choice is not specified. See Unresolved 2.
- ch09-18: fixed as declared gap (§4.2 TIME bullet): the stored form of a Time result in a non-`HH:mm:ss` declaration is "not stated". See Unresolved 3.
- ch09-20: fixed (§5.2 "Unmeasured cells … A checker's class choice in these cells is not specified").
- ch09-21: fixed (§3.2 last paragraph is a pointer to spec/10 §3.1). Content compared: spec/10 §3.1 holds the VALUE message with the rule's code, the two-pass reachability, no suppression by a later `And`, first-iterator address, row-loop termination, independent rules, and the Berlin measurement scope.
- ch09-22: fixed (parallel marking moved from §3.3 to §5.4).
- ch09-23: fixed (placement, containment, sibling-star and constructor routes moved from §6 to §5.1 and §5.5; §6 keeps only the anchoring sentence plus a pointer).
- ch09-24: deferred (owner is another chapter). The constant ladder and field-pair comparison walk stay in §1.4, tabulated; the move is under Other chapters.
- ch09-25: fixed. V2 result channels (old 09:127) and application placement (old 09:150) replaced by pointers to spec/01 §4.3 after checking that spec/01 §4.3 states every clause (five channels, `noErrorOccurred`, formal collection is not dependency evaluation, source-relative application to another destination, CLEARED/ERRORED/VALUE placement, no-action for an absent source, one- and two-level predecessor materialization, CLEARED-before-VALUE order independence, later validation without recomputation). The `Abs` and rounding direction half of old 09:28 is replaced by a pointer to spec/10 §4's propagation table; checked equal on every case old 09:28 names (symmetric zero → grow-only, fixed Base Year → fixed, grow-only stays grow-only, rounding preserves movement).
- C5 process voice (09 section): fixed throughout. Inline checkpoint/inbound/a12-dmkits links moved to one `Sources:` line per section (19 lines); Lean status removed at old 09:250, 09:258, 09:260 (the "checked reference account" sentences became rules plus measured scope); "Measured:" list at old 09:17 became "Measured shapes"; the `rule check` provenance aside at old 09:246 became a Sources note; calibration denominators at old 09:174 and 09:185 became "Measured scope" sentences; peer test links at old 09:81 and 09:99 moved to Sources (09:99 to its local record `src-addressed-numeric-binary`); "Confidence limit" sentences at old 09:30, 09:97, 09:233, 09:242 became scope statements; strategy-agreement narrative ("Both code-generation strategies agree", "Dynamic Groovy and generated Java agree", "the clean-room interpreter agrees") deleted; reader warnings ("This is the file to get exactly right", "the branch a carrier is most likely to get wrong", "they are the two a consumer … gets wrong", "Nothing here explains why") deleted.
- Negative existential 09:166 (`HH`): fixed (§4.1 last paragraph) — scoped to "the measured vocabulary of §6".
- Negative existential 09:188 (no-fit only under suppression): fixed (§4.3 NUMBER) — "reached when the computation suppresses …; whether a tolerance-banded alternative reaches it is unmeasured". See Unresolved 4.
- Negative existential 09:20 (ISO "cannot be authored"): fixed (§4.1) — refused at the three measured targets; the "cannot be authored" sentence deleted.
- Negative existential 09:190 ("unreachable"): fixed (§4.3 NUMBER) — restated as a property of the canonical rendering ("produces no invalid character, plus sign, signed zero or leading zero … so no other check applies").
- xc-4: not applicable within spec/09 beyond §1/§5.2, which already state the containment test and its closed exemptions; the spec/01 edit is under Other chapters. The `NoFieldFilled(Legs)` instance is not added (no witness).
- xc-6: fixed (§2 operand table: DATE column limited to Date-valued operations; Date-to-Number extractors and differences routed to the Number column, citing spec/03 §A.2 and spec/05 §3). See behavioural decision 4.
- ch01-3: not applicable within spec/09 except the pointer: §1.3 now points to spec/04 §1 for capability propagation and keeps the "outside a capable subexpression" qualifier. spec/01/04 edits under Other chapters.
- ch02-9: not applicable (spec/02's sentence already points to spec/09 §3.2, which keeps the formally-invalid-stored-operand rule).
- ch03-2: not applicable (spec/03 note only; spec/09 §5.1 keeps "a computation precondition has no row gate" that spec/03:85 links).
- ch03-10: fixed on the spec/09 side (§3.2 lead: an unavailable cell is any B.3 producer except the validation-scoped required finding, so a direct non-index compute read of a duplicate-index cell poisons by the general rule); spec/03 phase scope under Other chapters.
- ch04-1: not applicable within spec/09 (pointer added in §1.3); spec/04 edit under Other chapters.
- ch05-13: not applicable within spec/09 (§4.1 names the three operand gates and points to spec/05); table under Other chapters.
- ch05-16: not applicable within spec/09 (§4.1 keeps the computed-target zone case); carrier table under Other chapters.
- ch06-12: not applicable within spec/09 (§1.3 keeps the arity class names); move under Other chapters.
- ch06-7: not applicable within spec/09 (§1.3 names both arity gates `MVK_TOO_MANY_DIV_FOR_CALC` and `MVK_TOO_MANY_POW_FOR_CALC`); partition under Other chapters.
- ch07-26: not applicable within spec/09 (§3.3 keeps the implicit-guard bullet that spec/07:204 overlaps); pointer under Other chapters.
- ch08-1: deferred (owner spec/08). §5.4 keeps "malformed, duplicated or empty"; pointer to a single definition under Other chapters.
- ch10-11: fixed (this run). spec/10 §4.2's stored-side fixity, `referenced` reach and authored-shape inventory, `fillToFix` all-or-none and malformed-only suppression moved to §6 "The message's type and channels"; `10-new09.md` keeps the polarity rule (starred operand OMISSION, directional dispatch), a pointer, and the address-dialect witness as the spec/01 §3.1 part.
- ch12-2: not applicable within spec/09 (§1.3 names `MVK_TOO_MANY_DIV_FOR_CALC`); spec/12 edit under Other chapters.
- ch12-3: not applicable within spec/09 (§1.3 names `MVK_TOO_MANY_POW_FOR_CALC`); spec/12 edit under Other chapters.
- ch12-15: not applicable within spec/09 (§4.1 is the normative owner); spec/12 pointer under Other chapters.
- Feedback Q-014 (spec/09 L212, join key clear EMPTY or poison): fixed with the Lean side, marked unmeasured (§5.4). See behavioural decision 2.
- Feedback D (spec/09 §6 L222, keyword-named target segment): fixed (§6 sentence after the shape: `[F]` spelled by spec/08 §1, a keyword-named segment single-quoted).
- Feedback D (spec/09 §5 L206–218, partner joins the keyed level by shared index name, unkeyed ancestor included): fixed (§5.4 lead, with a link to spec/07 §2).
- Feedback B (tolerance operators infix wherever a rule text is shown): fixed (§6 shape writes `[F] mismatchᵢ operationᵢ` infix and defines `mismatchᵢ` as `!=` or the named tolerance operator), matching Lean `DmComputation.generatedRule?` (`A12Kernel/Reference/Dm/GeneratedComputationRule.lean`).
- 02-notes (spec/09:103 and 09:111, ch02-2): fixed (§3.2 lead: field-cell value and presence reads poison, group presence never poisons, pointing to spec/02 B.6 and the operator reference C column).
- 10-notes (spec/09:124, ch09-21): fixed (see ch09-21).
- 14-notes (`RepetitionNotUnique` in a computation): fixed (§1 prohibited-predicates bullet states the common-precondition refusal, marked unmeasured; `14-new09.md` sets the C cell to `n/a`, its note marking the common-precondition refusal unmeasured as spec/09 does; spec/07:190 covers a precondition outside a filter). See behavioural decision 8.

## Behavioural decisions

1. **Parallel-join invalid index scope (ch09-1).** Old 09:212: "an **invalid index cell in *any* joined group clears *every* instance** of the computation (deliberately broader than strictly necessary)". Old 09:144: "a malformed key in the computed field's **own on-path** index group truncates *below* the sibling level, so siblings stay distinguished and a clean sibling's target **survives with its value**". Side taken: the truncated-prefix rule (09:141–144), with "every instance" kept as the no-shared-repeatable-level case. Lean: `commonRepeatablePrefix`, `ParallelComputationMarkPlan.ofScopes`, `markForUnavailable` and `covers` in `A12Kernel/Semantics/ParallelComputationClearing.lean`.
2. **Dependent read of a skipped joined instance (feedback Q-014).** Old 09:141: "affected instances are instead marked after the loop" (no dependent rule; "marked" could be read as §3.2's invalid-target membership, which would poison). Feedback: the U01 worker chose poison by guess. Side taken: the instance "is skipped and stores no value", and "a dependent reads it as empty (unmeasured)"; §5.4 says the skip is not §3.2's invalid-target marking, and §3.2's "already marked invalid" now refers only to its own abort. Lean is consistent: a covered mark sets `indexInvalid` (`A12Kernel/Elaboration/ParallelComputationClearing.lean`), and `CheckedParallelNumericStep.execute` (`A12Kernel/Elaboration/ParallelNumericStep.lean`) and the joined row step (`A12Kernel/Elaboration/ParallelJoinedRowStep.lean:209`) emit a clean `.noValue` with an empty read-back in the plan overlay; "cause-blind" in `A12Kernel/Semantics/ParallelComputationClearing.lean` names the mark key, not poison. No checkpoint measures a dependent of such a target.
3. **Filtered aggregate over zero survivors (ch09-2).** Old 09:112: "A filtered aggregate whose candidate set is empty produces no value for that target row, and a dependent reads it as EMPTY." spec/07:130 (already decides): "the aggregate then answers over the survivors — zero of them included, which is an ordinary `0` for a count or a `Sum`". Side taken: spec/07 §3 for count and `Sum`, spec/03 §A.3 identities for the rest; no value only where the identity is no value (measured: `FirstFilledValue` into String). Cited from other chapters, not from Lean.
4. **Empty Date operand (xc-6).** Old 09:69 DATE column: "operation not evaluated → **CLEARED**". spec/03:59 (already decides): "the date/time **extractors** … and date **differences** | read as the fillable **`0`**"; spec/05 §3 bullet "Numeric component extractors and date differences map incomplete/not-given … to the same amount `0`". Side taken: DATE column limited to Date-valued operations; Date-to-Number operations in the Number column. Audit names Lean `DateDifferenceOperand.evaluate` as following spec/03/05.
5. **Full-Date field copy into a yearless target (ch09-6).** Old 09:162: "a full-Date field cannot be copied into a yearless Date target" (unconditional, in a paragraph opening "With Base Year 2024"). Old 09:177 and spec/05:167: "requires matching year presence unless the Base Year supplies `YEAR`". Side taken: the refusal is stated as measured, and whether a declared Base Year admits the copy is stated as unmeasured, because the measured row's Base Year setting is not recorded; no rule is taken from Lean (`temporalYearPresenceAgrees` and `TemporalComparisonOp.admitsFormats` in `A12Kernel/Semantics/TemporalFormat.lean` would admit it, but the computation field-copy admission def was not traced to them). Listed also under Unresolved.
6. **Scale gate beside a tolerance band (ch09-7).** Old 09:17: "A derived scale **larger** than the declared scale is always rejected". spec/04:145 (already decides): tolerance "deliberately bypasses the ordinary `==`/`!=` maximum-fractional-digit agreement gate"; old 09:242 ("`Exact` beside a band floors a finer operation") is consistent. Side taken: the gate is per alternative, and a banded alternative meets no scale agreement gate. Cited from spec/04.
7. **`MVK_ERROR_FIELD_NO_INDEX` topology (ch09-8).** Old 09:246: "`MVK_NO_WILDCARD` when the extent declares no index field, and `MVK_ERROR_FIELD_NO_INDEX` when it declares one". Old 09:217: "A level beside the target's group draws `MVK_ERROR_FIELD_NO_INDEX` when it declares an index field and the target's own path declares none". Side taken: 09:217. Lean: `UnboundOperandLevel.diagnostic?` and `passesWalk` (`A12Kernel/Elaboration/Flat/Types.lean`), `UnboundOperandLevel.walkRefusal?` (`A12Kernel/Elaboration/Flat/Model.lean`).
8. **`RepetitionNotUnique` in the common precondition (14-notes).** Old 09:31: "`CustomCondition` or `RepetitionNotUnique` in an alternative's precondition, and `CustomCondition` in the common precondition, draw `MVK_ERROR_INVALID_LANGUAGE_FEATURE`" (silent on RNU in the common precondition). Side taken: the same class, marked unmeasured. Lean: `lowerGuard` (`A12Kernel/Reference/Dm/Compute.lean:84`), locks in `A12Kernel/Reference/Dm/RepetitionNotUniqueLocks.lean`. No `docs/sources` checkpoint found measuring it. spec/14 C cell set to `n/a` in `14-new09.md`.
9. **Empty-precondition gate per declaration (ch09-5).** Old 09:211: "A missing precondition is legal only on the sole alternative; a multi-alternative table must guard every row" next to "concatenates all of those alternatives … into one first-match table". Old 09:51 (already decides): separate `GroupFilled(Form) => [X]` and unconditional `2` computations for one target are admitted in both orders. Side taken: the gate is per declaration and the combined table may hold unguarded rows. Decided by the chapter's own measured example and consistent with spec/01:172; no Lean def opened.

## Unresolved

1. Old 09:242 "`Exact` beside a band floors … where the same model without its band errors": whether that is a static refusal or a runtime rejected attempt is not recorded (the archived inbound record says only "errors" on a runtime differential). Kept, qualified as "not recorded" (§6).
2. ch09-17: the unconfigured interpretation-bearing DateRange route has only its declaration-order discriminator; kept as a declared gap (§4.2).
3. ch09-18: the stored form of a `Time(...)`/`TimeFromDateTime(...)` result in a target whose format is not `HH:mm:ss`; marked not stated (§4.2).
4. Negative existential 09:188: whether a tolerance-banded alternative reaches the Number no-fit branch; marked unmeasured (§4.3).
5. ch09-12: the order between containment and an unresolved name, and the position of the §1.4 wrong-kind classes among the stages; marked not stated (§1.2). Lean has a shared Number/String alternative walk, but the String side is "by assumption" in the implementation map, so the per-alternative interleaving stays labelled Number-only.
6. ch09-20: the unmeasured self-read cells; the checker's choice is stated as not specified (§5.2).
7. ch09-6: whether a declared Base Year admits a full-Date field copy into a yearless Date target is unmeasured (§4 lead bullet; behavioural decision 5).
8. The single-quoting of a keyword-named segment in the generated `[F]` is inferred from spec/08 §1 and marked unmeasured (§6).

## Rules not kept

None.

## Other chapters

- spec/01:178 (xc-4): replace "(guarding via its *containing group* is allowed)" with the closed exemption list (singular `GroupFilled`, positive fixed-root `AtLeastOneGroupFilled(Root)`, `CurrentRepetition`) and link `09-computations.md#52-the-target-self-read-gate`.
- spec/01:177 (ch01-3) and spec/04 §1 (ch04-1): state the capability algebra normatively in spec/04 §1 and fix 01:177's "holds once any non-capable field reference enters the operation"; spec/09 §1.3 already points to spec/04 §1 for propagation. Also say in 01:177 that a tolerance-banded alternative meets no scale gate (behavioural decision 6).
- spec/01 §3.2 (ch09-3, ch09-5): "No match ⇒ the target is **CLEARED**" should read as a clean no value that projects to CLEARED when the source target was filled; "every row of a multi-alternative table is guarded" should say per declaration (behavioural decision 9).
- spec/01 §3.1 (ch10-11): absorb the general channel facts — the address-dialect witness left in spec/10 §4.2's second bullet, and the general form of spec/09 §6's `referenced` reach and authored-shape inventory, which are computation-measured witnesses of 01 §3.1's structural projection; then spec/10 §4.2's second bullet becomes a pointer.
- spec/03:137 (ch03-10): add the phase scope for the duplicate-index third state (validation UNKNOWN; computation poison per spec/09 §3.2; compute index-column strictness per spec/09 §5.4).
- spec/04 §5 / spec/06:13 (ch06-12, ch06-7): move the arithmetic kind and arity gates (`MVK_NO_NUMBER_FOR_CALC`, `MVK_TOO_MANY_DIV_FOR_CALC`, `MVK_TOO_MANY_POW_FOR_CALC`, `MVK_NO_STRING_OR_NUMBER_FOR_ADD`) to spec/04 and state the kind partition over every declared kind; spec/09 §1.3 can then link them.
- spec/05 (ch05-13): add the per-unit temporal operand admission table; spec/09 §4.1's operand-gate sentence then points to it.
- spec/05 (ch05-16): add the nonexistent-zone-label carrier table; the computed-target row is spec/09 §4.1's DateTime-constant paragraph.
- spec/05 §1 or the comparison owner, and spec/07:122 (ch09-24): take ownership of the constant-assignment ladder and the field-pair comparison walk (spec/09 §1.4 tables); spec/09 §1.4 then points to it.
- spec/07:204 (ch07-26): point the implicit group-guard overlap to `09-computations.md#33-what-compute-reports`.
- spec/07 §2: the parallel-join section may link spec/09 §5.4 (`#54-parallel-joins`) for the computation's truncated-prefix marking.
- spec/08 §4.1/§4.2 (ch08-1): define the compromised index column once (malformed, duplicated, empty, and for partial validation non-relevant); spec/09 §5.4 then points to it.
- spec/11:33: repoint the "reached runtime failure" link from `09-computations.md#32-an-invalidity-clear-poisons` to `10-validation-and-polarity.md#31-truth-testing-and-message-classification` (spec/09 §3.2 now holds only a pointer for the validation side).
- spec/12:46, 12:76, 12:265 (ch12-2, ch12-3): name `MVK_TOO_MANY_DIV_FOR_CALC` and `MVK_TOO_MANY_POW_FOR_CALC` as spec/09 §1.3 does.
- spec/12:35 (ch12-15): point the temporal-constant rules to `09-computations.md#41-temporal-constants`.
- spec/14: `14-new09.md` (RNU C cell `n/a`). The C column's measured-scope sentence and its `§11 §3.2` links remain valid.
- spec-sync ledger: behavioural decisions 1, 2, 3, 4, 5, 6, 7, 8 and 9 change or narrow spec/09 text and need HIGH's `SPEC-` classification; 2 and 8 are Lean-derived and marked unmeasured.
- Lean docstrings (optional): `A12Kernel/Semantics/StringAlternatives.lean` links spec/09 §5 for alternative selection, now `#53-selection-across-alternatives-and-declarations`; the parallel-clearing modules could link `#54-parallel-joins`.

## Anchors

- `#1-the-ground-rules` (11 links: ARCHITECTURE, implementation/data-and-core, EXECUTE, spec/07 ×1, spec/14 ×3, others): kept at §1. The prohibited-predicate refusals (`CustomCondition`, `RepetitionNotUnique`), `RangeAsString`, and the declaration-context scope rule stay in §1's body. Self-read and cycle material moved into §1.1/§5.2 below the same anchor's chapter region.
- `#11-group-derived-scheduling-dependencies` (ANALYZE, internal): kept at §1.1; now also holds the cycle law.
- `#2-separate-operations-and-the-three-outcomes` (LEAN-FINDINGS): kept at §2 with heading text unchanged; the expression-versus-root String distinction stays there.
- `#31-a-precondition-clear-cascades-as-empty` (LEAN-FINDINGS, internal): kept at §3.1.
- `#32-an-invalidity-clear-poisons` (spec/02, spec/11, spec/14 ×2, LEAN-FINDINGS, sources): kept at §3.2; category-read poison, the poison class and the validation-runtime-failure pointer stay there.
- `#33-what-compute-reports` (spec/01, sources, LEAN-FINDINGS): kept at §3.3; the scale-sensitive change test and the cleared-instance accessor stay there.
- `#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape` (spec/04, spec/06, sources ×3): kept at §4; the Number scale-19 rule and the String maximum now sit in §4.3 under it.
- `#5-where-a-computation-runs--scope-and-the-parallel-join` (spec/01, spec/03, spec/07, Lean `StringAlternatives.lean`, sources, LEAN-FINDINGS): kept at §5; the row-gate sentence is §5.1, selection §5.3, the joined `GroupFilled` partner rule §5.4.
- `#6-the-implicit-validation-rule-precisely` (spec/01, spec/07, spec/10, spec/11, five Lean files, sources, implementation/computations): kept at §6; the generated shape, parse precedence, firing, tolerance and anchoring stay there, and the message channels moved in from spec/10 §4.2.
- New anchors: `#12-static-admission-order`, `#13-the-scale-gate`, `#14-wrong-kind-constants-and-field-sources`, `#41-temporal-constants`, `#42-temporal-targets`, `#43-number-string-enumeration-and-custom-targets`, `#51-operand-reach-scope-the-level-walk-and-placement`, `#52-the-target-self-read-gate`, `#53-selection-across-alternatives-and-declarations`, `#54-parallel-joins`, `#55-sibling-star-selection-and-repeatable-time-construction`.
- `10-new09.md` keeps the heading `#42-the-computations-implicit-self-validation-message`, which spec/09 §6 links. Every relative link in the three output files was checked to resolve against the current tree or the new files.

## HIGH review (2026-10-26)

- Preservation check by a fresh verifier: 186 old statements, 163 kept, 13 generalised with the cases checked, 10 declared changes, 0 lost; decisions 1, 2, 4, 5, 7 and 8 Lean-confirmed, and the cited sentences for 3, 6 and 9 exist and decide their cases.
- Corrected before commit: the stage headline no longer says stage-1 classes stand together; the reserved Custom report is excepted from the poisoning targets; joined instances under an invalid key are "skipped", so §3.2's invalid-target marking keeps one meaning; the full-Date-to-yearless refusal is measured while the Base-Year case is unmeasured; the joined precondition and operation atom lists stay separate; Time-only classification is scoped back; the generated `[F]` quoting is marked unmeasured; the four-deep diamond is restored; §6 links spec/10 §4.
- Decision 2 checked directly: a covered mark sets `indexInvalid`, and the step emits a clean no value with an empty read-back, distinct from the poison read-back of a value failure. Lean is consistent; the dependent read stays unmeasured.
- spec/10 §4.2's computation-message facts moved into §6 (ch10-11), and spec/14's `RepetitionNotUnique` C cell is `n/a` with the refusal marked unmeasured.
- Ledger: decisions 5–9 are `SPEC-2026-10-26-11`, decisions 1–4 `-12`.
