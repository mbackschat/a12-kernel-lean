import A12Kernel.Semantics.ValueList

/-! # A12Kernel.Proofs.ValueList — resolved value-list laws

These laws cover only the already-expanded, already-filtered runtime boundary. They do not prove star expansion, `Having` filtering, comparability checking, or authored-to-resolved lowering.
-/

namespace A12Kernel

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
  unfold evalValueListAtLeastOne
  split <;> simp

/-- `No` returns UNKNOWN exactly when either already-classified side contains UNKNOWN. This test precedes membership. -/
theorem valueListNo_unknown_iff
    (fields values : ResolvedValueListSide kind) :
    evalValueListNo fields values = .unknown ↔
      (fields.hasUnknown || values.hasUnknown) = true := by
  cases fieldsUnknown : fields.hasUnknown <;>
    cases valuesUnknown : values.hasUnknown <;>
    simp [evalValueListNo, fieldsUnknown, valuesUnknown] <;>
    split <;> simp

/-- `NotAll` needs a present field before an unknown values member can poison it. -/
theorem valueListNotAll_noPresent_notFired
    (fields values : ResolvedValueListSide kind)
    (noPresent : fields.hasPresent = false) :
    evalValueListNotAll fields values = .notFired := by
  simp [evalValueListNotAll, noPresent]

/-- Once a present field exists, `NotAll` returns UNKNOWN exactly for an UNKNOWN values member. -/
theorem valueListNotAll_unknown_iff_of_present
    (fields values : ResolvedValueListSide kind)
    (present : fields.hasPresent = true) :
    evalValueListNotAll fields values = .unknown ↔
      values.hasUnknown = true := by
  cases valuesUnknown : values.hasUnknown <;>
    simp [evalValueListNotAll, present, valuesUnknown] <;>
    split <;> simp

/-- Prepending a fields-side UNKNOWN leaves the complete `NotAll` verdict unchanged. -/
theorem valueListNotAll_prependUnknownField
    (fields values : ResolvedValueListSide kind) (cause : FormalCause) :
    evalValueListNotAll
        { fields with cells := .unknown cause :: fields.cells } values =
      evalValueListNotAll fields values := by
  cases fields
  simp [evalValueListNotAll, ResolvedValueListSide.hasPresent,
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
  simp [evalValueListAtLeastOne, having, hasMatch]

/-- A clean nonmatching `No` with `Having` metadata fires as OMISSION. -/
theorem valueListNo_having_fires_omission
    (fields values : ResolvedValueListSide kind)
    (having : (fields.hasHaving || values.hasHaving) = true)
    (fieldsKnown : fields.hasUnknown = false)
    (valuesKnown : values.hasUnknown = false)
    (noMatch : fields.anyMatches values = false) :
    evalValueListNo fields values = .fired .omission := by
  simp [evalValueListNo, having, fieldsKnown, valuesKnown, noMatch]

/-- A known `NotAll` witness with `Having` metadata fires as OMISSION. -/
theorem valueListNotAll_having_fires_omission
    (fields values : ResolvedValueListSide kind)
    (having : (fields.hasHaving || values.hasHaving) = true)
    (present : fields.hasPresent = true)
    (valuesKnown : values.hasUnknown = false)
    (outside : fields.anyOutside values = true) :
    evalValueListNotAll fields values = .fired .omission := by
  simp [evalValueListNotAll, having, present, valuesKnown, outside]

end A12Kernel
