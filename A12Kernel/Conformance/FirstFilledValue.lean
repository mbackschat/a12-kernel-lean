import A12Kernel.Semantics.FirstFilledValue

/-! # Resolved Number `FirstFilledValue` executable locks

These cases start after ordered expansion and `Having` filtering. They lock the prefix-sensitive single- and multi-slot scan plus its two projections without adding paths, authored lowering, filter evaluation, target application, or whole-rule orchestration.
-/

namespace A12Kernel.Conformance.FirstFilledValue

open A12Kernel

private def side
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail : Bool := false)
    (hasHaving : Bool := false) : ResolvedValueListSide .number :=
  { cells, hasUninstantiatedTail, hasHaving }

private def operands
    (first : ResolvedValueListSide .number)
    (rest : List (ResolvedValueListSide .number)) : FirstFilledNumberOperands :=
  { first, rest }

/- The first present Number wins and makes every later cell invisible. -/
example :
    evalFirstFilledNumber
      (side [.present 9, .present 3, .unknown .malformed]) =
        .value 9 false := by
  native_decide

/- An empty prefix preserves the selected amount but makes it not-given/fillable. -/
example :
    evalFirstFilledNumber (side [.empty, .present 7]) =
      .value 7 true := by
  native_decide

example :
    (evalFirstFilledNumber (side [.empty, .present 7])).asValidationOperand =
      .value 7 .both ∧
    NumericComparisonOp.greater.evalFixedRight
      (evalFirstFilledNumber (side [.empty, .present 7])).asValidationOperand 5 =
        .fired .omission := by
  native_decide

/- An empty suffix cannot displace an already selected first value. -/
example :
    evalFirstFilledNumber (side [.present 7, .empty]) =
      .value 7 false ∧
    NumericComparisonOp.greater.evalFixedRight
      (evalFirstFilledNumber (side [.present 7, .empty])).asValidationOperand 5 =
        .fired .value := by
  native_decide

/- Formal invalidity before selection suppresses validation and poisons computation. -/
example :
    evalFirstFilledNumber (side [.unknown .malformed, .present 7]) =
      .unavailable .malformed ∧
    (evalFirstFilledNumber
      (side [.unknown .malformed, .present 7])).asValidationOperand =
        .unknown .malformed ∧
    (evalFirstFilledNumber
      (side [.unknown .malformed, .present 7])).asComputationResult =
        .poison .malformed := by
  native_decide

/- The same invalidity after selection is not consumed. -/
example :
    evalFirstFilledNumber (side [.present 7, .unknown .malformed]) =
      .value 7 false ∧
    (evalFirstFilledNumber
      (side [.present 7, .unknown .malformed])).asComputationResult =
        .value 7 := by
  native_decide

/- Empty before invalid still reaches the invalid cell before any value. -/
example :
    evalFirstFilledNumber
      (side [.empty, .unknown .declaredConstraint, .present 7]) =
        .unavailable .declaredConstraint := by
  native_decide

/- An explicitly all-empty Number selection yields the fillable zero. -/
example :
    evalFirstFilledNumber (side [.empty, .empty]) =
      .value 0 true ∧
    NumericComparisonOp.less.evalFixedRight
      (evalFirstFilledNumber (side [.empty, .empty])).asValidationOperand 5 =
        .fired .omission ∧
    (evalFirstFilledNumber (side [.empty, .empty])).asComputationResult =
      .value 0 := by
  native_decide

/- An uninstantiated declared tail supplies the same all-empty potential. -/
example :
    evalFirstFilledNumber (side [] true) =
      .value 0 true := by
  native_decide

/- A filter on the sole admitted operand also makes its empty selection fillable. -/
example :
    evalFirstFilledNumber (side [] false true) =
      .value 0 true ∧
    NumericComparisonOp.less.evalFixedRight
      (evalFirstFilledNumber
        (side [] false true)).asValidationOperand 5 =
        .fired .omission := by
  native_decide

/- A resolved `Having` marks even a selected value fillable without changing computation. -/
example :
    evalFirstFilledNumber (side [.present 7] false true) =
      .value 7 true ∧
    (evalFirstFilledNumber
      (side [.present 7] false true)).asComputationResult =
        .value 7 ∧
    NumericComparisonOp.greater.evalFixedRight
      (evalFirstFilledNumber
        (side [.present 7] false true)).asValidationOperand 5 =
        .fired .omission := by
  native_decide

/- The total low-level state without cells or missingness metadata is fixed zero; checked authored lowering must not use it for a no-row star. -/
example :
    evalFirstFilledNumber (side []) =
      .value 0 false := by
  native_decide

/- Operand boundaries are semantically observable: a terminal first slot hides every later filter and cell. -/
example :
    evalFirstFilledNumberOperands
      (operands (side [.present 9]) [side [.unknown .malformed] false true]) =
        .value 9 false := by
  native_decide

/- A reached filter remains visible when its empty slot falls through to a later value. -/
example :
    evalFirstFilledNumberOperands
      (operands (side [] false true) [side [.present 9]]) =
        .value 9 true := by
  native_decide

/- An actual empty cell before a later value is fillable, but an omitted declared tail alone affects only an all-exhausted result. -/
example :
    evalFirstFilledNumberOperands
        (operands (side [.empty]) [side [.present 9]]) = .value 9 true ∧
      evalFirstFilledNumberOperands
        (operands (side [] true) [side [.present 9]]) = .value 9 false ∧
      evalFirstFilledNumberOperands
        (operands (side [] true) [side []]) = .value 0 true := by
  native_decide

/- Formal unavailability in a reached slot terminates before every later operand. -/
example :
    evalFirstFilledNumberOperands
      (operands (side [.unknown .declaredConstraint])
        [side [.present 9] false true]) =
      .unavailable .declaredConstraint := by
  native_decide

end A12Kernel.Conformance.FirstFilledValue
