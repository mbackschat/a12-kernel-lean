import A12Kernel.Elaboration.FirstFilledValue

/-! # Resolved Number `FirstFilledValue` laws

These laws characterize only one ordered, already-expanded and filtered Number operand plus its two projections. They do not prove path expansion, `Having` evaluation, partial relevance, multi-operand authoring, authored lowering, target application, or external kernel equivalence.
-/

namespace A12Kernel

private def firstFilledSide
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail : Bool := false)
    (hasHaving : Bool := false) : ResolvedValueListSide .number :=
  { cells, hasUninstantiatedTail, hasHaving }

/-- A present head is selected without observing any suffix or uninstantiated tail. -/
theorem firstFilledNumber_present_head
    (amount : Rat) (tail : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.present amount :: tail)
        hasUninstantiatedTail hasHaving) =
      .value amount hasHaving := by
  cases hasHaving <;> rfl

/-- An unavailable head terminates the scan without observing its suffix. -/
theorem firstFilledNumber_unknown_head
    (cause : FormalCause) (tail : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.unknown cause :: tail)
        hasUninstantiatedTail hasHaving) =
      .unavailable cause := by
  rfl

/-- Any empty prefix makes a later selected value not-given. -/
theorem firstFilledNumber_empty_then_present
    (amount : Rat) (tail : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.empty :: .present amount :: tail)
        hasUninstantiatedTail hasHaving) =
      .value amount true := by
  rfl

/-- Repeating an already-observed empty prefix cannot add another semantic distinction. -/
theorem firstFilledNumber_repeated_empty_prefix
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.empty :: .empty :: cells)
        hasUninstantiatedTail hasHaving) =
    evalFirstFilledNumber
      (firstFilledSide (.empty :: cells)
        hasUninstantiatedTail hasHaving) := by
  rfl

/-- An explicitly all-empty selection supplies the fillable Number zero. -/
theorem firstFilledNumber_explicit_empty_zero
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide [.empty] hasUninstantiatedTail hasHaving) =
      .value 0 true := by
  rfl

/-- A declared but uninstantiated tail supplies the same fillable Number zero. -/
theorem firstFilledNumber_uninstantiated_zero (hasHaving : Bool) :
    evalFirstFilledNumber (firstFilledSide [] true hasHaving) =
      .value 0 true := by
  rfl

/-- A filter on the admitted operand marks its exhausted empty selection fillable. -/
theorem firstFilledNumber_filtered_empty_zero :
    evalFirstFilledNumber (firstFilledSide [] false true) =
      .value 0 true := by
  rfl

/-- Available selections project to a numeric validation operand with exactly the carried fillability. -/
theorem firstFilledNumber_validation_projection
    (amount : Rat) (notGiven : Bool) :
    (FirstFilledNumberResult.value amount notGiven).asValidationOperand =
      .value amount (if notGiven then .both else .fixed) := by
  cases notGiven <;> rfl

/-- Formal unavailability becomes both an UNKNOWN validation operand and computation poison. -/
theorem firstFilledNumber_unavailable_projections
    (cause : FormalCause) :
    (FirstFilledNumberResult.unavailable cause).asValidationOperand =
        .unknown cause ∧
      (FirstFilledNumberResult.unavailable cause).asComputationResult =
        .poison cause := by
  constructor <;> rfl

/-- Validation distinguishes an earlier empty cell although computation deliberately forgets it. This checked non-law prevents the two projections from being collapsed. -/
theorem firstFilledNumber_empty_prefix_projection_separator
    (amount : Rat) :
    (evalFirstFilledNumber
      (firstFilledSide [.empty, .present amount])).asComputationResult =
        (evalFirstFilledNumber
          (firstFilledSide [.present amount])).asComputationResult ∧
    (evalFirstFilledNumber
      (firstFilledSide [.empty, .present amount])).asValidationOperand ≠
        (evalFirstFilledNumber
          (firstFilledSide [.present amount])).asValidationOperand := by
  rw [firstFilledNumber_empty_then_present amount [] false false,
    firstFilledNumber_present_head amount [] false false]
  constructor
  · rfl
  · intro equal
    have growEqual : true = false := by
      simpa only [FirstFilledNumberResult.asValidationOperand,
        NumericFillability.both, NumericFillability.fixed] using
        congrArg
          (fun operand =>
            match operand with
            | .value _ fillability => fillability.canGrow
            | .unknown _ => false)
          equal
    cases growEqual

/-- Successful checked-star evaluation is exactly the established prefix-terminating consumer over the shared checked resolved side. -/
theorem checkedNumericStarSource_evaluateFirstFilled_of_valid
    (checked : CheckedNumericStarSource model) (raw : RawSingleGroupContext)
    (valid : checked.validateContext raw = .ok ()) :
    checked.evaluateFirstFilled raw =
      .ok (evalFirstFilledNumber (checked.resolvedValueSide raw)) := by
  unfold CheckedNumericStarSource.evaluateFirstFilled
  rw [valid]
  rfl

end A12Kernel
