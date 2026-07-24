import A12Kernel.Semantics.ValueList

/-! # A12Kernel.Proofs.ValueList — resolved value-list laws

These laws cover only the already-expanded, already-filtered runtime boundary. They do not prove star expansion, `Having` filtering, comparability checking, or authored-to-resolved lowering.
-/

namespace A12Kernel

/-- `No` resolves the values side first and preserves its structural failure without touching the fields thunk. -/
theorem valueListQuantifier_resolveSidesOrdered_no_values_error
    (resolveFields : Unit → Except error fields) (cause : error) :
    ValueListQuantifier.no.resolveSidesOrdered resolveFields
      (fun () => (.error cause : Except error values)) =
        (.error cause : Except error (fields × values)) := by
  rfl

/-- `NotAll` resolves the fields side first and preserves its structural failure without touching the values thunk. -/
theorem valueListQuantifier_resolveSidesOrdered_notAll_fields_error
    (resolveValues : Unit → Except error values) (cause : error) :
    ValueListQuantifier.notAll.resolveSidesOrdered
      (fun () => (.error cause : Except error fields)) resolveValues =
        (.error cause : Except error (fields × values)) := by
  rfl

/-- The strict classified-cell scan is unavailable exactly when its input contains an unavailable cell. The accumulator step cannot create or erase availability. -/
theorem valueListCell_scanPresent_error_iff
    (step : state → ValueListAtom kind → state)
    (cells : List (ValueListCell kind)) (initial : state) :
    (∃ cause, ValueListCell.scanPresent step cells initial = .error cause) ↔
      cells.any ValueListCell.isUnknown = true := by
  induction cells generalizing initial with
  | nil => simp [ValueListCell.scanPresent]
  | cons cell cells inductionHypothesis =>
      cases cell with
      | present value =>
          simpa [ValueListCell.scanPresent, ValueListCell.isUnknown] using
            inductionHypothesis (step initial value)
      | empty =>
          simpa [ValueListCell.scanPresent, ValueListCell.isUnknown] using
            inductionHypothesis initial
      | unknown cause =>
          simp [ValueListCell.scanPresent, ValueListCell.isUnknown]

/-- A stream consisting only of empty cells preserves every caller-supplied accumulator. -/
theorem valueListCell_scanPresent_allEmpty
    (step : state → ValueListAtom kind → state)
    (cells : List (ValueListCell kind)) (initial : state)
    (allEmpty : cells.all ValueListCell.isEmpty = true) :
    ValueListCell.scanPresent step cells initial = .ok initial := by
  induction cells generalizing initial with
  | nil => rfl
  | cons cell cells inductionHypothesis =>
      cases cell with
      | present value => simp [ValueListCell.isEmpty] at allEmpty
      | empty =>
          simp only [List.all_cons, ValueListCell.isEmpty, Bool.true_and] at allEmpty
          exact inductionHypothesis initial allEmpty
      | unknown cause => simp [ValueListCell.isEmpty] at allEmpty

/-- A known prefix cannot hide or replace the cause of the first unavailable cell; the suffix is not consumed by this scan. -/
theorem valueListCell_scanPresent_firstUnknown
    (step : state → ValueListAtom kind → state)
    (before after : List (ValueListCell kind)) (initial : state)
    (cause : FormalCause)
    (beforeKnown : before.any ValueListCell.isUnknown = false) :
    ValueListCell.scanPresent step
      (before ++ .unknown cause :: after) initial = .error cause := by
  induction before generalizing initial with
  | nil => rfl
  | cons cell before inductionHypothesis =>
      cases cell with
      | present value =>
          simp only [List.any_cons, ValueListCell.isUnknown, Bool.false_or] at beforeKnown
          simpa [ValueListCell.scanPresent] using
            inductionHypothesis (step initial value) beforeKnown
      | empty =>
          simp only [List.any_cons, ValueListCell.isUnknown, Bool.false_or] at beforeKnown
          simpa [ValueListCell.scanPresent] using
            inductionHypothesis initial beforeKnown
      | unknown found => simp [ValueListCell.isUnknown] at beforeKnown

/-- Numeric membership is exactly equality after the shared scale-19 normalization. -/
theorem valueList_number_equal_iff_normalized_eq (left right : Rat) :
    ValueListAtom.equal (kind := .number) left right = true ↔
      normalizedComparisonValue left = normalizedComparisonValue right := by
  simp [ValueListAtom.equal, NumericComparisonOp.holds]

/-- An empty member contributes no atom for any admitted value-list kind. In particular, an empty Number member is not zero. -/
theorem valueList_contains_prependEmpty
    (values : ResolvedValueListSide kind) (candidate : ValueListAtom kind) :
    ({ values with cells := .empty :: values.cells } :
      ResolvedValueListSide kind).contains candidate =
        values.contains candidate := by
  cases values
  simp [ResolvedValueListSide.contains]

/-- `AtLeastOne` skips UNKNOWN cells on both sides and therefore never returns UNKNOWN. -/
theorem valueListAtLeastOne_never_unknown
    (fields values : ResolvedValueListSide kind) :
    evalValueListAtLeastOne fields values ≠ .unknown := by
  unfold evalValueListAtLeastOne evalClassifiedValueListAtLeastOne
  split <;> simp

/-- A fields-side match terminates `No` before a later unavailable cell. -/
theorem valueListNo_match_before_unknown
    (value : ValueListAtom kind) (cause : FormalCause) :
    evalValueListNo
      { cells := [.present value, .unknown cause]
        hasUninstantiatedTail := false, hasHaving := false }
      { cells := [.present value]
        hasUninstantiatedTail := false, hasHaving := false } =
      .notFired := by
  cases kind <;>
    simp [evalValueListNo, evalClassifiedValueListNo,
      scanValueListNoCells, valueListMembersContain,
      ResolvedValueListSide.presentValues, ResolvedValueListSide.hasUnknown,
      ValueListCell.isUnknown, ValueListAtom.equal, NumericComparisonOp.holds]

/-- Reversing the same fields cells exposes the unavailable cell before the match. -/
theorem valueListNo_unknown_before_match
    (value : ValueListAtom kind) (cause : FormalCause) :
    evalValueListNo
      { cells := [.unknown cause, .present value]
        hasUninstantiatedTail := false, hasHaving := false }
      { cells := [.present value]
        hasUninstantiatedTail := false, hasHaving := false } =
      .unknown := by
  rfl

/-- Values-side unavailability is consumed before the fields scan and therefore poisons even an immediate fields match. -/
theorem valueListNo_unknownMember_before_fields
    (value : ValueListAtom kind) (cause : FormalCause) :
    ValueListQuantifier.evalOrdered .no
      [{ cells := [.present value]
         hasUninstantiatedTail := false, hasHaving := false }]
      [{ cells := [.present value, .unknown cause]
         hasUninstantiatedTail := false, hasHaving := false }] =
      .unknown := by
  rfl

/-- `NotAll`'s ordered presence prepass leaves an unknown values member unread when no present field exists. -/
theorem valueListNotAll_noPresent_before_unknownMember
    (cause : FormalCause) :
    ValueListQuantifier.evalOrdered (kind := .token) .notAll
      [{ cells := [.empty]
         hasUninstantiatedTail := false, hasHaving := false }]
      [{ cells := [.unknown cause]
         hasUninstantiatedTail := false, hasHaving := false }] =
      .notFired := by
  rfl

/-- `NotAll` needs a present field before an unknown values member can poison it. -/
theorem valueListNotAll_noPresent_notFired
    (fields values : ResolvedValueListSide kind)
    (noPresent : fields.hasPresent = false) :
    evalValueListNotAll fields values = .notFired := by
  simp [evalValueListNotAll, evalClassifiedValueListNotAll, noPresent]

/-- Once a present field exists, `NotAll` returns UNKNOWN exactly for an UNKNOWN values member. -/
theorem valueListNotAll_unknown_iff_of_present
    (fields values : ResolvedValueListSide kind)
    (present : fields.hasPresent = true) :
    evalValueListNotAll fields values = .unknown ↔
      values.hasUnknown = true := by
  cases valuesUnknown : values.hasUnknown <;>
    simp [evalValueListNotAll, evalClassifiedValueListNotAll,
      present, valuesUnknown] <;>
    split <;> simp

/-- Prepending a fields-side UNKNOWN leaves the complete `NotAll` verdict unchanged. -/
theorem valueListNotAll_prependUnknownField
    (fields values : ResolvedValueListSide kind) (cause : FormalCause) :
    evalValueListNotAll
        { fields with cells := .unknown cause :: fields.cells } values =
      evalValueListNotAll fields values := by
  cases fields
  simp [evalValueListNotAll, evalClassifiedValueListNotAll,
    ResolvedValueListSide.hasPresent,
    ResolvedValueListSide.anyOutside]

/-- A present scalar subject cannot match a single empty field-valued member. -/
theorem valueListAtLeastOne_present_emptyMember
    (value : ValueListAtom kind) :
    evalValueListAtLeastOne
      { cells := [.present value], hasUninstantiatedTail := false, hasHaving := false }
      { cells := [.empty], hasUninstantiatedTail := false, hasHaving := false } =
        .notFired := by
  rfl

/-- The same empty member makes a present scalar outside the currently known set, but its fillability makes the NotIncluded fire omission-typed. -/
theorem valueListNotAll_present_emptyMember
    (value : ValueListAtom kind) :
    evalValueListNotAll
      { cells := [.present value], hasUninstantiatedTail := false, hasHaving := false }
      { cells := [.empty], hasUninstantiatedTail := false, hasHaving := false } =
        .fired .omission := by
  rfl

/-- A matching `AtLeastOne` with `Having` metadata fires as OMISSION. -/
theorem valueListAtLeastOne_having_fires_omission
    (fields values : ResolvedValueListSide kind)
    (having : (fields.hasHaving || values.hasHaving) = true)
    (hasMatch : fields.anyMatches values = true) :
    evalValueListAtLeastOne fields values = .fired .omission := by
  simp [evalValueListAtLeastOne, evalClassifiedValueListAtLeastOne,
    having, hasMatch]

/-- A reached filtered fields operand makes an exhausted ordered `No` scan omission-typed. -/
theorem valueListNo_filtered_nonmatch
    : ValueListQuantifier.evalOrdered (kind := .token) .no
      [{ cells := [.present "B"]
         hasUninstantiatedTail := false, hasHaving := true }]
      [{ cells := [.present "A"]
         hasUninstantiatedTail := false, hasHaving := false }] =
      .fired .omission := by
  rfl

/-- A known `NotAll` witness with `Having` metadata fires as OMISSION. -/
theorem valueListNotAll_having_fires_omission
    (fields values : ResolvedValueListSide kind)
    (having : (fields.hasHaving || values.hasHaving) = true)
    (present : fields.hasPresent = true)
    (valuesKnown : values.hasUnknown = false)
    (outside : fields.anyOutside values = true) :
    evalValueListNotAll fields values = .fired .omission := by
  simp [evalValueListNotAll, evalClassifiedValueListNotAll,
    having, present, valuesKnown, outside]

/-- Present membership is monotone when a resolved cell stream is extended without changing its existing cells. -/
theorem resolvedValueList_contains_of_cells_sublist
    (selected full : ResolvedValueListSide kind) (candidate : ValueListAtom kind)
    (subset : selected.cells.Sublist full.cells)
    (contains : selected.contains candidate = true) :
    full.contains candidate = true := by
  rw [ResolvedValueListSide.contains, List.any_eq_true] at contains ⊢
  rcases contains with ⟨cell, member, hMatches⟩
  exact ⟨cell, subset.subset member, hMatches⟩

/-- A present match found in two selected substreams remains a match in their complete streams. -/
theorem resolvedValueList_anyMatches_of_cells_sublist
    (selectedFields fullFields selectedValues fullValues :
      ResolvedValueListSide kind)
    (fieldsSubset : selectedFields.cells.Sublist fullFields.cells)
    (valuesSubset : selectedValues.cells.Sublist fullValues.cells)
    (hasMatch : selectedFields.anyMatches selectedValues = true) :
    fullFields.anyMatches fullValues = true := by
  rw [ResolvedValueListSide.anyMatches, List.any_eq_true] at hasMatch ⊢
  rcases hasMatch with ⟨cell, member, cellMatches⟩
  cases cell with
  | present value =>
      exact ⟨.present value, fieldsSubset.subset member,
        resolvedValueList_contains_of_cells_sublist selectedValues fullValues
          value valuesSubset cellMatches⟩
  | empty => simp at cellMatches
  | unknown cause => simp at cellMatches

/-- A selected fields-side outside witness remains outside when the values side is complete and the full fields stream only adds cells. -/
theorem resolvedValueList_anyOutside_of_fields_sublist
    (selectedFields fullFields values : ResolvedValueListSide kind)
    (fieldsSubset : selectedFields.cells.Sublist fullFields.cells)
    (outside : selectedFields.anyOutside values = true) :
    fullFields.anyOutside values = true := by
  rw [ResolvedValueListSide.anyOutside, List.any_eq_true] at outside ⊢
  rcases outside with ⟨cell, member, cellOutside⟩
  exact ⟨cell, fieldsSubset.subset member, cellOutside⟩

theorem resolvedValueList_hasPresent_of_anyOutside
    (fields values : ResolvedValueListSide kind)
    (outside : fields.anyOutside values = true) :
    fields.hasPresent = true := by
  rw [ResolvedValueListSide.anyOutside, List.any_eq_true] at outside
  rcases outside with ⟨cell, member, cellOutside⟩
  rw [ResolvedValueListSide.hasPresent, List.any_eq_true]
  cases cell with
  | present value => exact ⟨.present value, member, rfl⟩
  | empty => simp at cellOutside
  | unknown cause => simp at cellOutside

/-- With no masked cells, the classified-side route is definitionally the ordinary resolved quantifier route. -/
theorem valueList_evalClassified_noNonRelevant
    (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListQuantifierSide kind)
    (fieldsRelevant : fields.hasNonRelevant = false)
    (valuesRelevant : values.hasNonRelevant = false) :
    quantifier.evalClassified fields values =
      quantifier.eval fields.side values.side := by
  cases quantifier <;>
    simp [ValueListQuantifier.eval, ValueListQuantifier.evalClassified,
      evalClassifiedValueListAtLeastOne, evalClassifiedValueListNo,
      evalClassifiedValueListNotAll,
      ResolvedValueListQuantifierSide.hasUnknown,
      ResolvedValueListQuantifierSide.hasPresent,
      ResolvedValueListQuantifierSide.anyMatches,
      ResolvedValueListQuantifierSide.anyOutside,
      fieldsRelevant, valuesRelevant]

/-- A fired partial classified quantifier remains fired when masked cells are restored. Existential matches are monotone; `No` requires both sides complete; `NotAll` requires only its values side complete. -/
theorem valueList_classified_fired_implies_resolved_fired
    (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListQuantifierSide kind)
    (fullFields fullValues : ResolvedValueListSide kind)
    (fieldsSubset : fields.side.cells.Sublist fullFields.cells)
    (valuesSubset : values.side.cells.Sublist fullValues.cells)
    (fieldsComplete : fields.hasNonRelevant = false → fields.side = fullFields)
    (valuesComplete : values.hasNonRelevant = false → values.side = fullValues)
    (partialPolarity : Polarity)
    (fired : quantifier.evalClassified fields values = .fired partialPolarity) :
    ∃ fullPolarity, quantifier.eval fullFields fullValues = .fired fullPolarity := by
  cases quantifier with
  | atLeastOne =>
      have selectedMatch : fields.anyMatches values = true := by
        cases noMatch : fields.side.anyMatches values.side with
        | false =>
            simp [ValueListQuantifier.evalClassified,
              evalClassifiedValueListAtLeastOne,
              ResolvedValueListQuantifierSide.anyMatches, noMatch] at fired
        | true =>
            change fields.side.anyMatches values.side = true
            exact noMatch
      have fullMatch := resolvedValueList_anyMatches_of_cells_sublist
        fields.side fullFields values.side fullValues fieldsSubset valuesSubset
        selectedMatch
      refine ⟨if fullFields.hasHaving || fullValues.hasHaving then
          .omission else .value, ?_⟩
      simp [ValueListQuantifier.eval, ValueListQuantifier.evalClassified,
        evalClassifiedValueListAtLeastOne, fullMatch]
  | no =>
      cases fieldsRelevant : fields.hasNonRelevant with
      | true =>
          simp [ValueListQuantifier.evalClassified,
            evalClassifiedValueListNo,
            ResolvedValueListQuantifierSide.hasUnknown,
            fieldsRelevant] at fired
      | false =>
          cases valuesRelevant : values.hasNonRelevant with
          | true =>
              simp [ValueListQuantifier.evalClassified,
                evalClassifiedValueListNo,
                ResolvedValueListQuantifierSide.hasUnknown,
                valuesRelevant] at fired
          | false =>
              refine ⟨partialPolarity, ?_⟩
              rw [← fieldsComplete fieldsRelevant, ← valuesComplete valuesRelevant]
              rw [← valueList_evalClassified_noNonRelevant .no fields values
                fieldsRelevant valuesRelevant]
              exact fired
  | notAll =>
      cases valuesRelevant : values.hasNonRelevant with
      | true =>
          cases present : fields.side.hasPresent with
          | false =>
              simp [ValueListQuantifier.evalClassified,
                evalClassifiedValueListNotAll,
                ResolvedValueListQuantifierSide.hasPresent, present] at fired
          | true =>
              simp [ValueListQuantifier.evalClassified,
                evalClassifiedValueListNotAll,
                ResolvedValueListQuantifierSide.hasPresent,
                ResolvedValueListQuantifierSide.hasUnknown,
                present, valuesRelevant] at fired
      | false =>
          have selectedOutside : fields.anyOutside values = true := by
            cases present : fields.side.hasPresent <;>
              cases valuesUnknown : values.side.hasUnknown <;>
              cases outside : fields.side.anyOutside values.side <;>
              simp [ValueListQuantifier.evalClassified,
                evalClassifiedValueListNotAll,
                ResolvedValueListQuantifierSide.hasPresent,
                ResolvedValueListQuantifierSide.hasUnknown,
                ResolvedValueListQuantifierSide.anyOutside,
                present, valuesUnknown, outside, valuesRelevant] at fired
            change fields.side.anyOutside values.side = true
            exact outside
          have selectedPresent := resolvedValueList_hasPresent_of_anyOutside
            fields.side values.side selectedOutside
          have selectedValuesKnown : values.hasUnknown = false := by
            cases valuesUnknown : values.side.hasUnknown with
            | false =>
                simp [ResolvedValueListQuantifierSide.hasUnknown,
                  valuesRelevant, valuesUnknown]
            | true =>
                simp [ValueListQuantifier.evalClassified,
                  evalClassifiedValueListNotAll,
                  ResolvedValueListQuantifierSide.hasPresent,
                  ResolvedValueListQuantifierSide.hasUnknown,
                  selectedPresent, valuesRelevant, valuesUnknown] at fired
          have valuesEq := valuesComplete valuesRelevant
          have fullOutside : fullFields.anyOutside fullValues = true := by
            rw [← valuesEq]
            exact resolvedValueList_anyOutside_of_fields_sublist
              fields.side fullFields values.side fieldsSubset selectedOutside
          have fullPresent := resolvedValueList_hasPresent_of_anyOutside
            fullFields fullValues fullOutside
          have fullValuesKnown : fullValues.hasUnknown = false := by
            rw [← valuesEq]
            simpa [ResolvedValueListQuantifierSide.hasUnknown,
              valuesRelevant] using selectedValuesKnown
          refine ⟨if fullFields.hasHaving || fullValues.hasHaving ||
              fullValues.hasMissingPotential then .omission else .value, ?_⟩
          simp [ValueListQuantifier.eval, ValueListQuantifier.evalClassified,
            evalClassifiedValueListNotAll, fullPresent, fullValuesKnown,
            fullOutside]

end A12Kernel
