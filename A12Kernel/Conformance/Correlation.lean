import A12Kernel.Semantics.Correlation

/-! # Captured outer-correlation conformance locks -/

namespace A12Kernel.Conformance.Correlation

open A12Kernel

private def items : RepeatableLevel := 10

private def count : FlatNumberField :=
  { id := 0, info := { scale := 0, signed := false } }

private def payload : FlatNumberField :=
  { id := 1, info := { scale := 0, signed := false } }

private def marker : FlatNumberField :=
  { id := 2, info := { scale := 0, signed := false } }

private def checkedNumber : RawCell → CheckedCell :=
  formalCheck { kind := .number count.info }

private def rawContextOf (values : List RawCell) : SingleGroupValidationContext where
  group := items
  candidates := (List.range values.length).map (· + 1)
  read row fieldId :=
    if fieldId != count.id then checkedNumber .empty
    else match values[row - 1]? with
      | some value => checkedNumber value
      | none => checkedNumber .empty

private def contextOf (values : List Rat) : SingleGroupValidationContext :=
  rawContextOf (values.map fun value => .parsed (.num value))

private def distinct : SingleGroupValidationContext :=
  contextOf [5, 6, 9]

private def duplicates : SingleGroupValidationContext :=
  contextOf [5, 5, 9]

private def emptyAndZero : SingleGroupValidationContext :=
  rawContextOf [.empty, .parsed (.num 0)]

private def malformedSecond : SingleGroupValidationContext :=
  rawContextOf [.parsed (.num 5), .rejected .malformed]

private def selfExcludedConsumerContext
    (rows : List (Rat × RawCell)) : SingleGroupValidationContext where
  group := items
  candidates := (List.range rows.length).map (· + 1)
  read row fieldId :=
    if fieldId == count.id then
      match rows[row - 1]? with
      | some (key, _) => checkedNumber (.parsed (.num key))
      | none => checkedNumber .empty
    else if fieldId == payload.id then
      match rows[row - 1]? with
      | some (_, value) => checkedNumber value
      | none => checkedNumber .empty
    else if fieldId == marker.id then
      checkedNumber (.parsed (.num 1))
    else
      checkedNumber .empty

private def malformedFirstConsumer : SingleGroupValidationContext :=
  selfExcludedConsumerContext [
    (5, .rejected .malformed), (5, .parsed (.num 9))]

private def malformedSecondConsumer : SingleGroupValidationContext :=
  selfExcludedConsumerContext [
    (5, .parsed (.num 9)), (5, .rejected .malformed)]

private def validConsumers : SingleGroupValidationContext :=
  selfExcludedConsumerContext [
    (5, .parsed (.num 8)), (5, .parsed (.num 9))]

private def distinctConsumerKeys : SingleGroupValidationContext :=
  selfExcludedConsumerContext [
    (5, .parsed (.num 8)), (6, .parsed (.num 9))]

private def mixedConsumers : SingleGroupValidationContext :=
  selfExcludedConsumerContext [
    (5, .rejected .malformed),
    (5, .parsed (.num 9)),
    (5, .parsed (.num 10))]

private def emptyFirstMarker : SingleGroupValidationContext :=
  { validConsumers with read := fun row fieldId =>
      if row == 1 && fieldId == marker.id then checkedNumber .empty
      else validConsumers.read row fieldId }

private def innerCount : HavingNumberRef :=
  { origin := .inner, field := count }

private def outerCount : HavingNumberRef :=
  { origin := .outer, field := count }

private def checkedHaving (condition : CorrelatedHaving)
    (inner : condition.usesInner = true) (outer : condition.usesOuter = true) :
    OriginCheckedCorrelatedHaving :=
  { condition, usesInner := inner, usesOuter := outer }

private def selfIncluded : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.compareNumbers .equal innerCount outerCount) (by decide) (by decide) }

private def selfExcluded : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.and
        (.compareRepetitions .notEqual .inner .outer)
        (.compareNumbers .equal innerCount outerCount)) (by decide) (by decide) }

private def selfExcludedPayload : SingleCorrelatedStar :=
  { valueField := payload, having := selfExcluded.having }

private def smallerInner : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.compareNumbers .lessThan innerCount outerCount) (by decide) (by decide) }

private def captured (rows : SingleGroupValidationContext) (outerRow : RowIndex) :
    CapturedSingleGroupContext :=
  { rows, outerRow }

private def checkError : Except CorrelationCheckError OriginCheckedCorrelatedHaving →
    Option CorrelationCheckError
  | .ok _ => none
  | .error error => some error

example : distinct.WellFormed := by
  native_decide

example : ¬({ distinct with candidates := [0] }).WellFormed := by
  native_decide

example : ¬({ distinct with candidates := [1, 1] }).WellFormed := by
  native_decide

example : selfIncluded.select (captured distinct 1) = [1] := by
  native_decide

example : selfIncluded.select (captured distinct 2) = [2] := by
  native_decide

example : selfIncluded.firingRows distinct = [1, 2, 3] := by
  native_decide

/-- Numeric comparison resolves empty to zero, so the empty row matches itself and the
    explicitly stored zero row at the filter boundary. -/
example : selfIncluded.select (captured emptyAndZero 1) = [1, 2] := by
  native_decide

/-- A malformed inner operand is unknown and therefore is not selected. -/
example : selfIncluded.select (captured malformedSecond 1) = [1] := by
  native_decide

/-- A malformed outer operand makes every comparison unknown, so no candidate is kept. -/
example : selfIncluded.select (captured malformedSecond 2) = [] := by
  native_decide

/-- Self-exclusion is authored, not inferred by the evaluator. -/
example : selfIncluded.select (captured distinct 2) ≠ [] := by
  native_decide

example : selfExcluded.firingRows distinct = [] := by
  native_decide

example : selfExcluded.select (captured duplicates 1) = [2] := by
  native_decide

example : selfExcluded.select (captured duplicates 2) = [1] := by
  native_decide

example : selfExcluded.select (captured duplicates 3) = [] := by
  native_decide

example : selfExcluded.firingRows duplicates = [1, 2] := by
  native_decide

/-- Row 1's malformed consumed value is outside its self-excluded selection; row 2's
    valid value is selected, so the guarded quantifier fires. -/
example :
    selfExcludedPayload.evalGuardedAnyFilledOn marker
      (captured malformedFirstConsumer 1) = .tru := by
  native_decide

/-- From row 2, the same malformed value is selected and makes the consumer unknown. -/
example :
    selfExcludedPayload.evalGuardedAnyFilledOn marker
      (captured malformedFirstConsumer 2) = .unknown := by
  native_decide

example :
    selfExcludedPayload.firingRowsOn marker malformedFirstConsumer = [1] := by
  native_decide

/-- Swapping only which consumed row is malformed mirrors the firing row. -/
example :
    selfExcludedPayload.firingRowsOn marker malformedSecondConsumer = [2] := by
  native_decide

example :
    selfExcludedPayload.firingRowsOn marker validConsumers = [1, 2] := by
  native_decide

/-- A selected valid cell satisfies the existential consumer even when another selected
    cell is malformed; kept invalidity is not global poison for this operator. -/
example :
    selfExcludedPayload.evalGuardedAnyFilledOn marker
      (captured mixedConsumers 3) = .tru := by
  native_decide

/-- Selection stability is load-bearing in the footprint theorem. The left selected
    consumer premise would be vacuous, yet changing only the filter keys changes the
    selection and the result. -/
example :
    selfExcludedPayload.select (captured distinctConsumerKeys 1) = [] ∧
    selfExcludedPayload.select (captured validConsumers 1) = [2] ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured distinctConsumerKeys 1) = .fls ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured validConsumers 1) = .tru := by
  native_decide

/-- Guard-observation agreement is also load-bearing when selection and selected
    consumer cells are identical. -/
example :
    selfExcludedPayload.select (captured emptyFirstMarker 1) =
        selfExcludedPayload.select (captured validConsumers 1) ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured emptyFirstMarker 1) = .fls ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured validConsumers 1) = .tru := by
  native_decide

/-- This asymmetric case distinguishes inner/outer routing from reversal or collapse. -/
example : smallerInner.select (captured distinct 1) = [] := by
  native_decide

example : smallerInner.select (captured distinct 2) = [1] := by
  native_decide

example : smallerInner.select (captured distinct 3) = [1, 2] := by
  native_decide

example : smallerInner.firingRows distinct = [2, 3] := by
  native_decide

example :
    checkError (CorrelatedHaving.compareNumbers .equal outerCount outerCount).check =
      some .missingInner := by
  decide

example :
    checkError (CorrelatedHaving.compareNumbers .equal innerCount innerCount).check =
      some .missingOuter := by
  decide

end A12Kernel.Conformance.Correlation
