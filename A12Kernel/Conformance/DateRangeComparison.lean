import A12Kernel.Elaboration.DateRangeConstructionComparison

/-! # Resolved and checked DateRange construction-equality locks -/

namespace A12Kernel.Conformance.DateRangeComparison

open A12Kernel

private def full (year : Int) (month day : Nat)
    (admissible : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admissible

private def june1 := full 2024 6 1 (by native_decide)
private def june29 := full 2024 6 29 (by native_decide)
private def june30 := full 2024 6 30 (by native_decide)

private def constructed : ResolvedDateRangeConstruction :=
  { start := june1, finish := june30 }

private def constructedChangedFinish : ResolvedDateRangeConstruction :=
  { start := june1, finish := june29 }

private def storedSame : ResolvedDateRange :=
  { start := june1, finish := june30 }

private def storedChangedFinish : ResolvedDateRange :=
  { start := june1, finish := june29 }

private def fullDate := TemporalComponents.fullDate

private def dateField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal .date fullDate }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd"
    partialMode := .full } }

private def leftStart := dateField 1 "LeftStart"
private def leftFinish := dateField 2 "LeftFinish"
private def rightStart := dateField 3 "RightStart"
private def rightFinish := dateField 4 "RightFinish"

private def storedRange : FlatFieldDecl := {
  id := 5
  groupPath := ["Order"]
  name := "StoredRange"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }

private def checkedModel : FlatModel := {
  fields := [leftStart, leftFinish, rightStart, rightFinish, storedRange]
  timeZoneId := "Europe/Berlin" }

private def dateValue (epochMillis : Int)
    (year : Int) (month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian }

private def dateRaw (value : DateValue) : RawCell :=
  .parsed (.temporal (.date value))

private def storedForRaw : RawCell → String
  | .parsed (.temporal (.date value)) =>
      match value.toFullDate? with
      | some date => FullDateTargetFormat.yearMonthDayDashes.renderText date
      | none => "invalid-date"
  | .rejected _ => "bad"
  | .empty | .presentEmpty => ""
  | .parsed _ => "wrong-kind"

private def inputCell (field : FlatFieldDecl)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field := field.id, path := [] }
  stored := storedForRaw raw
  raw }

private def checkedInputFrom (cells : List ClassifiedCellInput) :
    Option (CheckedDocument checkedModel) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler checkedModel).toOption
  checkDocument prepared "en_US" { instantiatedRows := [], cells } |>.toOption

private def checkedInput?
    (leftStartRaw leftFinishRaw rightStartRaw rightFinishRaw : RawCell) :
    Option (CheckedDocument checkedModel) :=
  checkedInputFrom [
    inputCell leftStart leftStartRaw,
    inputCell leftFinish leftFinishRaw,
    inputCell rightStart rightStartRaw,
    inputCell rightFinish rightFinishRaw ]

private def checkedMixedInput? (startRaw finishRaw : RawCell)
    (stored : String) (storedRaw : RawCell) :
    Option (CheckedDocument checkedModel) :=
  checkedInputFrom [
    inputCell leftStart startRaw,
    inputCell leftFinish finishRaw,
    { address := { field := storedRange.id, path := [] }, stored, raw := storedRaw } ]

private def checkedOperation? (op : EqualityOp) :=
  (elaborateDateRangeConstructionComparison checkedModel
    leftStart.id leftFinish.id rightStart.id rightFinish.id op).toOption

private def checkedMixedOperation? (position : DateRangeConstructionPosition)
    (op : EqualityOp) :=
  (elaborateDateRangeConstructionStoredComparison checkedModel
    leftStart.id leftFinish.id storedRange.id position op).toOption

private def checkedResult? (op : EqualityOp)
    (leftStartRaw leftFinishRaw rightStartRaw rightFinishRaw : RawCell) :
    Option DateRangeConstructionComparisonResult := do
  let input ← checkedInput?
    leftStartRaw leftFinishRaw rightStartRaw rightFinishRaw
  let operation ← checkedOperation? op
  (operation.evaluate input).toOption

private def checkedMixedResult? (position : DateRangeConstructionPosition)
    (op : EqualityOp) (startRaw finishRaw : RawCell)
    (stored : String) (storedRaw : RawCell) :
    Option DateRangeConstructionStoredComparisonResult := do
  let input ← checkedMixedInput? startRaw finishRaw stored storedRaw
  let operation ← checkedMixedOperation? position op
  (operation.evaluate input).toOption

private def startValue := dateValue 1717192800000 2024 6 1
private def changedStartValue := dateValue 1717279200000 2024 6 2
private def finishValue := dateValue 1719698400000 2024 6 30
private def changedFinishValue := dateValue 1719612000000 2024 6 29
private def storedSameValue : DateRangeValue := {
  start := startValue, finish := finishValue }
private def storedChangedStartValue : DateRangeValue := {
  start := changedStartValue, finish := finishValue }
private def storedChangedValue : DateRangeValue := {
  start := startValue, finish := changedFinishValue }

/- Construction-versus-field equality and inequality are exact complements on the maintained full-Date source pair. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .left constructed storedSame = .fired .value ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .left constructed storedSame = .notFired := by
  native_decide

/- Checked mixed execution preserves authored side, both rich operands, exact finish comparison, and complementary equality. -/
example :
    ((checkedMixedResult? .left .equal
      (dateRaw startValue) (dateRaw finishValue)
      "01.06.2024-30.06.2024" (.parsed (.dateRange storedSameValue))).map fun result =>
        (result.position, result.construction.start,
          result.stored, result.verdict)) =
      some (.left, .value startValue,
        .value storedSameValue, .fired .value) ∧
    ((checkedMixedResult? .right .notEqual
      (dateRaw startValue) (dateRaw finishValue)
      "01.06.2024-29.06.2024" (.parsed (.dateRange storedChangedValue))).map fun result =>
        (result.position, result.verdict)) =
      some (.right, .fired .value) ∧
    (checkedMixedResult? .right .equal
      (dateRaw startValue) (dateRaw finishValue)
      "02.06.2024-30.06.2024" (.parsed (.dateRange storedChangedStartValue))).map
        (fun result => result.verdict) = some .notFired ∧
    (checkedMixedResult? .left .notEqual
      (dateRaw startValue) (dateRaw finishValue)
      "02.06.2024-30.06.2024" (.parsed (.dateRange storedChangedStartValue))).map
        (fun result => result.verdict) = some (.fired .value) := by
  native_decide

/- Mixed execution compares reconstructed instants, not the construction input's incoming instant. -/
example :
  let alteredStart := { startValue with instant := { epochMillis := 1001 } }
  (checkedMixedResult? .left .equal
    (dateRaw alteredStart) (dateRaw finishValue)
    "01.06.2024-30.06.2024" (.parsed (.dateRange storedSameValue))).map
      (fun result => (result.construction.start, result.verdict)) =
    some (.value startValue, .fired .value) := by
  native_decide

/- Formal construction input dominates an empty stored range; stored formal invalidity remains independently visible. -/
example :
    ((checkedMixedResult? .left .equal
      (.rejected .malformed) (dateRaw finishValue)
      "" .presentEmpty).map fun result =>
        (result.construction.start, result.stored, result.verdict)) =
      some (.unknown .malformed, .empty, .unknown) ∧
    ((checkedMixedResult? .right .equal
      (dateRaw startValue) (dateRaw finishValue)
      "garbage" (.rejected .dateRangeSeparator)).map fun result =>
        (result.stored, result.verdict)) =
      some (.unknown .dateRangeSeparator, .unknown) := by
  native_decide

/- Changing only the finish endpoint separates whole-range identity from start-only comparison. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .left constructed storedChangedFinish = .notFired ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .right constructed storedChangedFinish = .fired .value := by
  native_decide

/- Exchanging the stored and constructed operands preserves both legal operators. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .right constructed storedSame = .fired .value ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .right constructed storedChangedFinish = .fired .value := by
  native_decide

/- Two constructions compare both ordered endpoints through the same exact equality seam. -/
example :
    EqualityOp.equal.evalDateRangeConstructions
        constructed constructed = .fired .value ∧
      EqualityOp.notEqual.evalDateRangeConstructions
        constructed constructed = .notFired ∧
      EqualityOp.equal.evalDateRangeConstructions
        constructed constructedChangedFinish = .notFired ∧
      EqualityOp.notEqual.evalDateRangeConstructions
        constructedChangedFinish constructed = .fired .value := by
  native_decide

/- The checked route certifies all four declarations, reads one immutable document, and retains every exact endpoint beside the equality verdict. -/
example : ((checkedResult? .equal
    (dateRaw { startValue with basis := .legacyHybrid }) (dateRaw finishValue)
    (dateRaw startValue) (dateRaw finishValue)).map fun result =>
      (result.left.start, result.left.finish,
        result.right.start, result.right.finish, result.verdict)) =
    some (.value startValue, .value finishValue,
      .value startValue, .value finishValue, .fired .value) := by
  native_decide

/- Changing only the second construction's finish separates whole-range equality and inequality through checked execution. -/
example :
    (checkedResult? .equal
      (dateRaw startValue) (dateRaw finishValue)
      (dateRaw startValue) (dateRaw changedFinishValue)).map (·.verdict) =
        some .notFired ∧
    (checkedResult? .notEqual
      (dateRaw startValue) (dateRaw finishValue)
      (dateRaw startValue) (dateRaw changedFinishValue)).map (·.verdict) =
        some (Verdict.fired .value) := by
  native_decide

/- Construction re-resolves a source label under the checked declaration profile instead of retaining a distinct incoming source instant. -/
example :
  let alteredStart := { startValue with instant := { epochMillis := 1001 } }
  EqualityOp.equal.evalDateRangeValues
      (.value { start := startValue, finish := finishValue } true)
      (.value { start := alteredStart, finish := finishValue } true) = .notFired ∧
    ((checkedResult? .equal
      (dateRaw startValue) (dateRaw finishValue)
      (dateRaw alteredStart) (dateRaw finishValue)).map fun result =>
        (result.right.start, result.verdict)) =
        some (.value startValue, .fired .value) := by
  native_decide

/- Any empty endpoint remains visible and suppresses the comparison instead of constructing a partial range. -/
example : ((checkedResult? .equal
    (dateRaw startValue) .presentEmpty
    (dateRaw startValue) (dateRaw finishValue)).map fun result =>
      (result.left.finish, result.verdict)) =
    some (.empty, .notFired) := by
  native_decide

/- Formal unavailability dominates emptiness within one construction, and the full observation remains available to Explain. -/
example : ((checkedResult? .equal
    .presentEmpty (.rejected .malformed)
    (dateRaw startValue) (dateRaw finishValue)).map fun result =>
      (result.left.start, result.left.finish, result.verdict)) =
    some (.empty, .unknown .malformed, .unknown) := by
  native_decide

/- The checked operation retains computation poison and projects it to validation UNKNOWN even when the same construction also has an empty endpoint. -/
example : (checkedOperation? .equal).map (fun operation =>
    let left : DateRangeConstructionObservation := {
      start := .empty
      finish := .poison .computedDependency }
    let right : DateRangeConstructionObservation := {
      start := .value startValue
      finish := .value finishValue }
    let result := operation.evaluateObserved left right
    (result.left.finish, result.verdict)) =
      some (.poison .computedDependency, .unknown) := by
  native_decide

/- Failure while certifying the final endpoint remains attributed to that authored position. -/
example : (match elaborateDateRangeConstructionComparison checkedModel
    leftStart.id leftFinish.id rightStart.id 99 .equal with
  | .ok _ => none
  | .error error => some error) =
    some (.right (.finish
      (.targetPolicy (.resolve (.unknownFieldId 99))))) := by
  native_decide

/- A typed Date with unreal decoded parts is a structural endpoint fault, not empty or formal unavailability. -/
example :
  let unreal := dateValue 0 2024 2 30
  (do
    let input ← checkedInput? (dateRaw unreal) (dateRaw finishValue)
      (dateRaw startValue) (dateRaw finishValue)
    let operation ← checkedOperation? .equal
    pure (match operation.evaluate input with
      | .ok _ => none
      | .error error => some error)) =
      some (some (.endpointDateUnavailable leftStart.id unreal)) := by
  native_decide

end A12Kernel.Conformance.DateRangeComparison
