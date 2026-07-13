import A12Kernel.Semantics.Iteration

/-! # Single-level iteration conformance locks

This capsule admits one repeatable level, a numeric starred operand, and an
uncorrelated `Having` condition. `$`, nested repetition, computation, and general
aggregate elaboration are deliberately unrepresentable here.
-/

namespace A12Kernel.Conformance.Iteration

open A12Kernel

private def items : RepeatableLevel := 10

private def weight : FlatNumberField :=
  { id := 0, info := { scale := 0, signed := false } }

private def count : FlatNumberField :=
  { id := 1, info := { scale := 0, signed := false } }

private def row (index : Nat) : Env := [(items, index)]

private def checkedNumber : RawCell → CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := false } }

private def source : SingleGroupValidationContext where
  group := items
  candidates := [1, 2, 3, 4]
  read index fieldId :=
    match index with
    | 1 => if fieldId = weight.id then checkedNumber (.parsed (.num 1))
        else checkedNumber (.parsed (.num 3))
    | 2 => if fieldId = weight.id then checkedNumber (.parsed (.num 2))
        else checkedNumber (.parsed (.num 10))
    | 3 => if fieldId = weight.id then checkedNumber (.parsed (.num 1))
        else checkedNumber (.parsed (.num 4))
    | 4 => if fieldId = weight.id then checkedNumber (.parsed (.num 1))
        else checkedNumber .empty
    | _ => checkedNumber .empty

private def malformedDroppedSource : SingleGroupValidationContext where
  group := source.group
  candidates := source.candidates
  read index fieldId :=
    match index with
    | 2 => if fieldId = weight.id then checkedNumber (.parsed (.num 2))
        else checkedNumber (.rejected .malformed)
    | _ => source.read index fieldId

private def malformedKeptSource : SingleGroupValidationContext where
  group := malformedDroppedSource.group
  candidates := malformedDroppedSource.candidates
  read index fieldId :=
    match index with
    | 2 => if fieldId = weight.id then checkedNumber (.parsed (.num 1))
        else checkedNumber (.rejected .malformed)
    | _ => malformedDroppedSource.read index fieldId

private def malformedFilterSource : SingleGroupValidationContext where
  group := source.group
  candidates := source.candidates
  read index fieldId :=
    match index with
    | 2 => if fieldId = weight.id then checkedNumber (.rejected .malformed)
        else checkedNumber (.parsed (.num 10))
    | _ => source.read index fieldId

private def weightIs (expected : Rat) : FlatCondition :=
  .compare (.number .equal weight expected)

private def filteredCounts (expected : Rat) : SingleStar :=
  { valueField := count, having := some (weightIs expected) }

private def allCounts : SingleStar :=
  { valueField := count, having := none }

example : source.candidates.map source.envAt = [row 1, row 2, row 3, row 4] := by
  decide

/-- A same-group star is not shorthand for the current row. -/
example : source.candidates ≠ [2] := by
  decide

example : (filteredCounts 1).select source = [1, 3, 4] := by
  native_decide

example : allCounts.sumSelected source = .value 17 := by
  native_decide

example : (filteredCounts 1).sumSelected source = .value 7 := by
  native_decide

example : (filteredCounts 1).evalSumEquality source .equal 7 = .tru := by
  native_decide

example : (filteredCounts 1).evalSumEquality source .equal 17 = .fls := by
  native_decide

example : (filteredCounts 9).sumSelected source = .value 0 := by
  native_decide

/-- Row 2's invalid consumed cell is harmless because the filter drops that row first. -/
example : (filteredCounts 1).sumSelected malformedDroppedSource = .value 7 := by
  native_decide

/-- The same invalid consumed cell suppresses the aggregate when its row is kept. -/
example : (filteredCounts 1).sumSelected malformedKeptSource =
    .unknown .malformed := by
  native_decide

/-- An unknown filter result is not true, so its row is dropped before consumption. -/
example : (filteredCounts 1).sumSelected malformedFilterSource =
    .value 7 := by
  native_decide

end A12Kernel.Conformance.Iteration
