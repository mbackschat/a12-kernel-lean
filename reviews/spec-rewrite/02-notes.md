# spec/02 rewrite — change notes

Draft: `02-new.md` (pilot). Old chapter: `spec/02-logic-and-formal-errors.md` at `1a9199a7`. Structure: A.1–A.3 and B.1–B.6 keep their headings; A.4 is split into nine `####` subsections (expansion, ranges, slot classification, validation tally, filtered lists, computation scans, group-list quantifiers, `NumberOfFilledGroups` runtime, static admission); B.3 gains `#### Over-repetition` and `#### String ingestion boundary`. Every section ends its rules with one `Sources:` line. The prose guard (`scripts/check-no-kernel-prose.sh`) was not run: it reads `../a12-kernel/`, which this brief forbids. The draft adds no message sentences, only codes already in the old text.

## Findings

- ch02-1: fixed. B.2's single aggregate row is split into consumer classes (all-cells combiner, stop-at-first, skip-invalid, group presence, computation), each with measured members and the statement that the class is per operator; "the enclosing rule is suppressed" became "the operand is UNKNOWN" plus a pointer to B.4. Checklist item added. See behavioural decision 1.
- ch02-2: fixed in A.4.8 (computation arm), B.2 (last table row) and B.6 (new third bullet): field-cell reads, value or presence, poison; `GroupFilled`, `GroupNotFilled`, `NumberOfFilledGroups` never poison; a malformed stored descendant is content, a descendant failed through a computed dependency is not. The "presence test is not a read" rationale is removed. The spec/09 side is under "Other chapters". See behavioural decision 2.
- ch02-3: fixed in B.2. The definition no longer says "present"; a third-state cell is one carrying a finding from a B.3 producer and need not hold a value. Required-and-empty is stated as validation-scoped, and non-relevance as a call-local source that is not a cell state (the tally counts it with `u`, spec/10 §5 owns the rest). B.3 is itself the cause list, so no pointer to SEMANTICS-MAP was needed; map wording is under "Other chapters".
- ch02-4: fixed in the A.4.9 locus table ("unguarded", with the guarded form admitted) and a pointer to §9 (spec/07 §5) for the iteration gate and its positive-guard lift.
- ch02-5: fixed in the chapter intro and the A.1 body: verdict domain (four results), truth by B.5, both polarity rules with a pointer to spec/10 §3, and the collapse law (no composed rule separates FALSE from UNKNOWN; Lean `Verdict.collapseUnknown` in `A12Kernel/Core.lean`, theorems `conj_collapseUnknown`, `disj_collapseUnknown` in `A12Kernel/Proofs/Verdict.lean` and `evalVerdict_collapseUnknown` in `A12Kernel/Proofs/ConditionTree.lean`). "Two-valued" is gone from the body; the A.1 heading keeps it because the heading is a linked anchor (see Unresolved).
- ch02-6: fixed in A.4.9: one ordered gate table for the `FieldFilled`/`FieldNotFilled` slot, one condition-by-carrier matrix for the trio, the pair, `GroupFilled` and the count, an explicit "known gate orders" list, and locus tables. Cells the old text does not decide are "—"; untested orderings are stated as unmeasured.
- ch02-8: fixed in A.4.9 ("Arms" paragraph and the arm column of the ancestor-starred table): duplicate, root, wildcard and arity rows on both arms (per the both-arms checkpoint); nested-descendant admission on the computation arm; locus tables on the rule arm.
- ch02-9: fixed. The open "clears or aborts" sentence is replaced by a pointer to §11 (spec/09 §3.2), which settles it.
- ch02-10: fixed. A.4.8 defines "value" (the count) and "extent" (the largest reachable value) and uses them consistently, including in A.4.7 and the old 02:66 wording.
- ch02-11: fixed in B.1: "node address (a field, row or group instance)".
- ch02-12: not applicable to spec/02 (the defect is 07:240); under "Other chapters".
- ch02-13: fixed. Precedence: B.3 "First failure wins" points String/Enumeration to spec/06 (and keeps the String clause order in B.3), Number to spec/04 §4, Date to spec/05 §4, others unspecified. Star gate versus containment gate: kept, marked unmeasured. Nested binding: kept, marked unmeasured. 02:109's "not established" computation cases: stated as the general rule with "these two computation cases are unmeasured" (behavioural decision 3). 02:67's confidence list: kept as a scope sentence beside the general rule.
- ch02-14: partly fixed. The ~2,500-word `NumberOfFilledGroups` block is restructured into A.4.8 (runtime, with an arm-comparison table) and A.4.9 (static tables). The String ingestion paragraph stays in B.3 because spec/06:35 lacks the raw-type gate, the full-check gate, the Enumeration line-break precedence and the display path; B.3 now points to spec/06 for message keys. Full dedupe is deferred to the spec/06 rewrite (see "Other chapters"). A.3 storage tokens and B.3 stay in 02, as the finding recommends.
- ch02-15: fixed. The a12-dmkits test links moved to the `Sources:` line of the B.3 String subsection, with the confidence limit (display-path CRLF preservation rests only on that differential) stated there. No local inbound record exists for IF124/IF125, so the links stay.
- xc-1 (02 side): fixed. B.3 Over-repetition now says the set is not narrowed by partial validation and that this is the exception to the coverage gate spec/10 §5 applies to the rest of the formal channel. The 10:162 side is under "Other chapters".
- ch01-1 (02 side): fixed. A.4.5 states that partial validation skips every filtered rule before any other admission step and points to spec/10 §5 for the ordered admission. The 01:194 side is under "Other chapters".
- ch01-16 (02 side): not applicable; B.3 already owns the rule and keeps its anchor. The 01:133 side is under "Other chapters".
- ch03-9 (02 side): fixed in A.4.1: a group operand of `NumberOfFilledFields` or `NumberOfValueInFields` expands recursively like the field-fill quantifiers; nested non-repeatable subgroups under these counts are marked unmeasured (per 04:143). Behavioural decision 4. The 03:67 side is under "Other chapters".
- ch07-1 (02 side): not applicable; A.4.2's table states the range once per operator. The 07:273 side is under "Other chapters".
- ch07-19: fixed in A.4.5: under an instantiated-range predicate a missing coordinate never enters the tally; whether the filter still executes there is left to spec/07 §3's traversal extent. Behavioural decision 5.
- ch10-12: fixed. The unavailable-member rule (stays in the list, settles nothing, decided exactly when the known members settle it, with the three-member witness) now lives in A.4.3; B.6's "An invalid cell drops out" is reworded to "stays where it is read and settles nothing". Behavioural decision 6. The 10:155–157 side is under "Other chapters".
- Feedback (spec/10 §5, `FieldValuesNotUnique` under a relevant set): addressed as a reader-confusion signal. B.2 now defines "skip" (removed from the comparison exactly like an empty cell, never makes the predicate UNKNOWN), says why skipping and UNKNOWN propagation coincide when no duplicate is at stake (A.1's collapse law), and names the separating case: an invalid member beside a duplicate among the others fires under skipping and would be silent under propagation. No rule changed. Lean `scanValuesNotUnique` (`A12Kernel/Semantics/NumericAggregate.lean`) carries no UNKNOWN result. The spec/10 phrase is under "Other chapters".
- C5 process voice: all inline checkpoint and inbound links moved to `Sources:` lines; deleted narration: the peer-renderer address explanation, "measured rather than inherited/carried" phrasing, refuted-reading narration, the Kernel-internal `compute()` conversion explanation, "on a run whose refusing rows prove the gate was live", "All three facts are measured", "Measured at kernel 30.8.1".
- Rule 5 negative existential: A.3's "no A12-supported configuration channel carries them into the formal check" (no measurement cited) became "no configuration channel that carries them into the formal check is known". The rule (validation ignores them) is unchanged.
- Rule 7 notes: B.5's information-order and monotonicity statement (normative per the checklist) moved from the note into B.5's rules; B.3's requiredness ordering, already in the rules, gained its rationale sentence in the rules; Lean def names (`formalCheck`, `observeCell`, `.overRepetition`, `.required`, `K.not`) removed from notes and replaced by neutral descriptions. The B.5 `K` sketch is kept as an illustrative non-normative sketch (its names are not repository defs).

## Behavioural decisions

1. B.2 aggregate/count row versus operator-specific behaviour.
   - Old A (02:163): "the **whole aggregate is non-evaluable** — the enclosing rule is suppressed, wherever in the selection the cell sits"
   - Old B (02:169; 02:194): "`FirstFilledValue` fires when the malformed cell follows the first filled row" / "it makes the reading operand UNKNOWN and Kleene `And`/`Or` decides the rest"
   - Side taken: B — per consumer class, and the operand (not the rule) becomes UNKNOWN.
   - Lean: `numberOfFilledFields` (`A12Kernel/Semantics/FieldFillQuantifier.lean`, all-cells → unknown), `scanDistinctCells`/`evalDistinctCountAggregate` (`A12Kernel/Semantics/NumericAggregate.lean`, all-cells), `scanFirstFilledObservations` (`A12Kernel/Semantics/FirstFilledScan.lean`, first non-empty decides), `scanValuesNotUnique` (`A12Kernel/Semantics/NumericAggregate.lean`, skip), `numberOfFilledGroups` (`A12Kernel/Semantics/GroupPresence.lean`), `Verdict.conj`/`Verdict.disj` (`A12Kernel/Core.lean`).
2. Computation presence reads.
   - Old A (02:111): "it governs a **read** ([§11](09-computations.md)), and a presence test is not a read."
   - Old B (02:125): "Every reached invalid slot in these computation scans poisons the computation instance."
   - Side taken: field-cell presence reads poison (B); group presence (`GroupFilled`, `GroupNotFilled`, `NumberOfFilledGroups`) never poisons; a computed-dependency failure supplies no group content.
   - Lean: `CellObservation.evalComputationFilled`/`evalComputationNotFilled` and `evalFieldFilled` (`A12Kernel/Semantics/ComputationCondition.lean`), `CellObservation.asComputationFillSlot` (`A12Kernel/Semantics/ComputationFillQuantifier.lean`), `GroupPresenceOperator.evalComputation` and `CellObservation.presentForComputation` (`A12Kernel/Semantics/GroupPresence.lean`). Kernel measurement: `docs/sources/computation-scheduling-probes.md#src-group-presence-computation-guards` (2026-10-03), now cited in A.4.8 and B.6.
3. Computation starred `NumberOfFilledGroups` operand on unmeasured shapes.
   - Old A (02:109): "takes that group's **instantiated row count**: no rows counts `0`, one instantiated but wholly empty row counts `1`"
   - Old B (02:109): "Not established by these rows: a row holding only formally invalid content, and a starred group owning a repeatable descendant."
   - Side taken: the general row-count rule covers both shapes (the contribution reads no cell; a repeatable descendant does not multiply it), marked "these two computation cases are unmeasured".
   - Lean: `GroupCountOperandReading.starredRows` (`A12Kernel/Semantics/GroupPresence.lean`), `readGroupCountOperand` (`A12Kernel/Elaboration/NumericComputation/Evaluation.lean`, `.starred` → `inCapacityRowCount`).
4. Group operand expansion for the counts (ch03-9).
   - Old A (02:59): "**A group operand means "every field inside it, recursively."**"
   - Old B (03:67): "A fixed group operand expands to its direct field entities for both `NumberOfValueInFields` and `NumberOfFilledFields`"
   - Side taken: A — recursive, with nested non-repeatable subgroups marked unmeasured for these counts.
   - Lean: `CheckedFilledFieldCountGroupSource.expansionOwned` over `FlatModel.groupSubtreeFields` (`A12Kernel/Elaboration/FilledFieldGroupCount.lean`); `CheckedTokenEntityGroup.expansionOwned` (`A12Kernel/Elaboration/TokenEntityGroup.lean`); the Boolean value count also uses `groupSubtreeFields` (`A12Kernel/Elaboration/BooleanValueCount.lean`).
5. Filters at missing coordinates under instantiated-range predicates (ch07-19).
   - Old A (02:83): "Apply the filter to the range the predicate asks for; only TRUE keeps a slot."
   - Old B (07:202): "**A filter can execute on a coordinate with no stored row.**"
   - Side taken: a missing coordinate never enters an instantiated-range tally (A); whether the filter executes there is not decided in spec/02 and is left to spec/07 §3.
   - Lean: `CheckedFieldFillOperand.validationRange?` (`A12Kernel/Elaboration/FieldFillList.lean`): with `declared = false` the missing count is `0`; only the declared-range path calls `selectedMissingCount?`.
6. Unavailable list member (ch10-12).
   - Old A (02:231): "**Validation excludes.** An invalid cell drops out: tallies count it in neither bucket"
   - Old B (10:157): "**What this refutes is the operand being dropped from a quantifier's operand list**"
   - Side taken: B — the member stays in the list and settles nothing (the bucket rule of A is unchanged).
   - Lean: `ValidationFillTally` with its separate `unknown` bucket and `FieldFillQuantifier.evalValidation` (`A12Kernel/Semantics/ValidationFillQuantifier.lean`).

## Unresolved

- A.1 heading "Connectives are two-valued; parentheses are mandatory" keeps "two-valued" (ch02-5) because spec/07:118 links its anchor. Recommendation: rename the heading and add an explicit `<a id="a1-connectives-are-two-valued-parentheses-are-mandatory"></a>` before it; owner decision.
- B.1 "ordinarily use a fixed, non-authorable message" conflicts with spec/06:35 (a pattern failure renders the declaration's own error text) and SEMANTICS-MAP:178 (selected constraints and requiredness may carry per-locale authored text). Not in the finding list; kept as written.
- B.3 producer list: not declared closed. Lean `FormalCause` (`A12Kernel/Cell.lean`) is closed but has members that do not map one-to-one onto the six listed producers (`customValidation`, the predefined-type fallback; `computedDependency`, the computation-only mark, which B.3 now mentions in one sentence). A later pass can close the list once spec/06 states the fallback.
- B.4: the old "treat validation read traces as unobserved until a focused engine probe exposes them" is overtaken by spec/07:146, which measures a raising validation leaf whose short-circuit is observable. The draft keeps the old scope ("the tables do not fix whether validation physically reads a decided-away operand") and adds a pointer to spec/07 §3; no rule chosen.
- A.4.9 trio, "a root beside a disjoint operand": the old text says the trio rejects roots and names `MVK_ROOT_GROUP_REFERENCED` only for a sole root and for a starred root in either position; the class for an unstarred root beside a disjoint operand is not stated and is left open.
- A.4.9 count, "a lone empty root": the old text says a lone empty group or root "draws its empty class"; the draft names the two empty classes `MVK_GROUP_IS_EMPTY`, `MVK_ROOT_GROUP_IS_EMPTY` from elsewhere in the same paragraph. Verify that a lone empty root draws `MVK_ROOT_GROUP_IS_EMPTY` before the next commit.
- A.3: "a lone long s draws `feldJaNeinFalsch`" is kept verbatim; whether "lone" means a token consisting of U+017F alone is not stated in the old text.

## Rules not kept

None. Deleted text that carried no rule: the Kernel-internal explanation of why the computation count does not poison ("during `compute()` the invalid cells are converted so that nothing is treated as irrelevant…"), replaced by the field/group rule of decision 2; the peer-renderer address narrative (the Kernel spelling rule is kept); the refuted-reading narration ("A reading that required a row at the *deepest* repeatable level is refuted there", implied by the kept outer-row rule); and evidence-liveness narration ("against a live control", "on a run whose refusing rows prove the gate was live"). The live-control sentence for the count's root gate carried one rule (a non-root group beside another root's star is admitted), which is kept in the A.4.9 matrix.

## Other chapters

- spec/10:162 (xc-1): limit the partial-validation formal-channel gate to cell-conversion findings and state the over-repetition exception with a pointer to spec/02 B.3 (Over-repetition).
- spec/10:155–157 (ch10-12): replace the erroneous-member paragraphs with a pointer to spec/02 A.4.3 (`#a43-classifying-a-slot`), keeping only partial-specific content.
- spec/10 §5 (feedback): the phrase "An uncovered cell is skipped as a formally invalid one is (spec/02)" should link spec/02 B.2's `FieldValuesNotUnique` paragraph and may name the separating case (a duplicate among the other members).
- spec/01:194 (ch01-1): state the ordered admission of spec/10 §5 (skip filtered rules, require the error field relevant, then override the content gate) or point to it.
- spec/01:133 (ch01-16): point §2.2 to spec/02 B.3 as the single owner of over-repetition findings.
- spec/03:67 (ch03-9): recursive expansion per spec/02 A.4.1 (decision 4), or label the direct-field statement measured-only for flat groups; nested fixed groups stay unmeasured as 04:143 says.
- spec/07:273 (ch07-1): replace "consider all possible repetitions" with a pointer to spec/02 A.4.2's per-operator range table.
- spec/07:202 (ch07-19): state whether a filter executes at a missing coordinate under an instantiated-range predicate, or mark it unknown; spec/02 A.4.5 now defers this to spec/07 §3.
- spec/07:240 (ch02-12): "on each of the row's declared cells" → "on each node the document writes at or beneath the row" (spec/02 B.3).
- spec/09:103 and 09:111 (ch02-2): state that a field-cell presence read poisons like a value read and that group presence never poisons, pointing to spec/02 B.6; 09's "§3's third state generally" can then point to B.2/B.3.
- SEMANTICS-MAP §4 item 2 and the 3VL/Kleene glossary row (ch02-5): drop "connectives are two-valued"; item 1 and the not-check-relevant row (ch02-3): align with spec/02 B.2's definition (a finding, not necessarily a present value; non-relevance is call-local).
- spec/06:35 (ch02-14): absorb the raw-type gate, full-check gate, Enumeration line-break precedence and display path now in spec/02 B.3 so that spec/02 can reduce its String paragraph to a pointer.
- spec/14 (planned operator table): B.2's consumer classes (all-cells, stop-at-first, skip-invalid, group presence) and their measured members are candidates for the table's invalid-read column.
- Lean docstring: `groupPresenceUndecided` (`A12Kernel/Semantics/GroupPresence.lean`) links `spec/02` without an anchor; it could link `#a48-numberoffilledgroups`.

## Anchors

| Anchor | Linked from | Now |
|---|---|---|
| `#a1-connectives-are-two-valued-parentheses-are-mandatory` | spec/07:118 | A.1, heading unchanged |
| `#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges` | spec/09:111, spec/07:268, spec/07:273, docs/LEAN-FINDINGS.md:642 and :654, docs/sources/group-list-and-capacity-probes.md:60, docs/sources/computation-scheduling-probes.md:451 | A.4, heading unchanged; content now in A.4.1–A.4.9 beneath it |
| `#b1-what-a-formal-error-is` | docs/PLAN.md:199, docs/consumer-probes/ANALYZE.md:232, docs/consumer-probes/EXECUTE.md:499 | B.1, heading unchanged |
| `#b3-what-puts-a-cell-in-the-third-state` | docs/LEAN-FINDINGS.md:202, spec/03:143, docs/sources/inbound-handbacks.md:824, spec/06:12, spec/06:54 | B.3, heading unchanged |
| `#b5-the-strong-kleene-tables-the-exact-algebra` | docs/consumer-probes/EXECUTE.md:360 | B.5, heading unchanged |
| `#part-b--3-formal-errors-and-the-unknown-state` | docs/sources/message-cache-probes.md:95 | Part B, heading unchanged |

New anchors: `#a41-operand-expansion`, `#a42-the-two-iteration-ranges`, `#a43-classifying-a-slot`, `#a44-validation-the-unfiltered-field-fill-tally`, `#a45-validation-filtered-field-fill-lists`, `#a46-computation-ordered-field-fill-scans`, `#a47-group-list-quantifiers`, `#a48-numberoffilledgroups`, `#a49-static-admission-of-group-and-field-slot-operands`, `#over-repetition`, `#string-ingestion-boundary`. All other old headings (A.2, A.3, B.2, B.4, B.6, the checklist) are unchanged.

## HIGH review (2026-10-26)

- Preservation check by a fresh verifier: 225 old statements, 208 kept, 8 generalised with the cases checked, 7 declared changes, 1 altered and 1 lost; all six decisions Lean-confirmed.
- Corrected before commit: the lone starred count operand is exempt from arity rather than admitted (altered); the empty-group class on every group carrier, lost from the count, is restored as an A.4.9 row consistent with spec/08; the settle-by-known-members law is limited to the fill quantifiers, `NumberOfFilledFields` following B.2's all-cells class; the empty-group gate is named rule-arm only; the starred malformed-row computation cell is marked unmeasured.
- Unresolved items settled: A.1 is renamed with its linked anchor kept as an explicit id; B.1 now says formal errors carry no rule-authored message, the text being built in or the declaration's own template for a pattern, Enumeration value or requiredness check (spec/11 Part A); the lone empty root's class is `MVK_ROOT_GROUP_IS_EMPTY`, measured in the K22 static-class capture row `s7-root-cnt`. The B.3 producer list, the B.4 trace scope, the trio's unstarred root beside a disjoint operand and the lone long s stay unresolved as listed above.
- ch07-19 is deferred to spec/07 §3, not fixed in spec/02.
- Ledger: decisions 1 and 6 are `SPEC-2026-10-26-01`, decision 2 `-02`, decision 4 `-03`, decision 5 `-04`, decision 3 `-05`.
