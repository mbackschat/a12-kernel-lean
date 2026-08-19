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
private def dottedDateField (id : FieldId) (name : String) : FlatFieldDecl := {
  dateField id name with
    temporalTargetPolicy := some {
      format := "dd.MM.yyyy"
      partialMode := .full } }
private def dottedStart := dottedDateField 11 "DottedStart"
private def dottedFinish := dottedDateField 12 "DottedFinish"

private def yearFragmentField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal .date fullDate }
  temporalTargetPolicy := some {
    format := "yyyy"
    partialMode := .yearOptional } }

private def leftYearStart := yearFragmentField 6 "LeftYearStart"
private def leftYearFinish := yearFragmentField 7 "LeftYearFinish"
private def rightYearStart := yearFragmentField 8 "RightYearStart"
private def rightYearFinish := yearFragmentField 9 "RightYearFinish"
private def yearMonthFragmentField (id : FieldId)
    (name : String) : FlatFieldDecl := {
  yearFragmentField id name with
    temporalTargetPolicy := some {
      format := "yyyy-MM"
      partialMode := .yearOptional } }
private def leftMonthStart := yearMonthFragmentField 13 "LeftMonthStart"
private def leftMonthFinish := yearMonthFragmentField 14 "LeftMonthFinish"
private def rightMonthStart := yearMonthFragmentField 15 "RightMonthStart"
private def rightMonthFinish := yearMonthFragmentField 16 "RightMonthFinish"
private def wrongModeMonthFragment : FlatFieldDecl := {
  yearMonthFragmentField 17 "WrongModeMonthFragment" with
    temporalTargetPolicy := some {
      format := "yyyy-MM"
      partialMode := .dayOptional } }
private def monthFragment : FlatFieldDecl := {
  yearFragmentField 10 "MonthFragment" with
    temporalTargetPolicy := some {
      format := "MM"
      partialMode := .yearOptional } }
private def leftMonthOnlyStart := monthFragment
private def leftMonthOnlyFinish : FlatFieldDecl := {
  monthFragment with id := 18, name := "LeftMonthOnlyFinish" }
private def rightMonthOnlyStart : FlatFieldDecl := {
  monthFragment with id := 19, name := "RightMonthOnlyStart" }
private def rightMonthOnlyFinish : FlatFieldDecl := {
  monthFragment with id := 20, name := "RightMonthOnlyFinish" }
private def monthDayFragmentField (id : FieldId) (name : String) : FlatFieldDecl := {
  yearFragmentField id name with
    temporalTargetPolicy := some {
      format := "MM-dd"
      partialMode := .yearOptional } }
private def leftMonthDayStart := monthDayFragmentField 21 "LeftMonthDayStart"
private def leftMonthDayFinish := monthDayFragmentField 22 "LeftMonthDayFinish"
private def rightMonthDayStart := monthDayFragmentField 23 "RightMonthDayStart"
private def rightMonthDayFinish := monthDayFragmentField 24 "RightMonthDayFinish"

private def storedRange : FlatFieldDecl := {
  id := 5
  groupPath := ["Order"]
  name := "StoredRange"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }

private def storedMonthRange : FlatFieldDecl := {
  storedRange with
  id := 25
  name := "StoredMonths"
  dateRangePolicy := some { format := "MM", separator := "/" } }

private def storedMonthDayRange : FlatFieldDecl := {
  storedRange with
  id := 26
  name := "StoredMonthDays"
  dateRangePolicy := some { format := "MM-dd", separator := "/" } }

private def storedIsoRange : FlatFieldDecl := {
  storedRange with
  id := 27
  name := "StoredIsoRange"
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def checkedModel : FlatModel := {
  fields := [leftStart, leftFinish, rightStart, rightFinish, storedRange,
    leftYearStart, leftYearFinish, rightYearStart, rightYearFinish,
    leftMonthStart, leftMonthFinish, rightMonthStart, rightMonthFinish,
    wrongModeMonthFragment, leftMonthOnlyStart, leftMonthOnlyFinish,
    rightMonthOnlyStart, rightMonthOnlyFinish, leftMonthDayStart,
    leftMonthDayFinish, rightMonthDayStart, rightMonthDayFinish,
    dottedStart, dottedFinish, storedMonthRange, storedMonthDayRange,
    storedIsoRange]
  timeZoneId := "Europe/Berlin"
  baseYear := some 2024 }

private def checkedModel2023 : FlatModel := {
  checkedModel with baseYear := some 2023 }

private def checkedModelNoBase : FlatModel := {
  checkedModel with baseYear := none }

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

private def checkedInputFromFor (model : FlatModel)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  checkDocument prepared "en_US" { instantiatedRows := [], cells } |>.toOption

private def checkedInputFrom (cells : List ClassifiedCellInput) :
    Option (CheckedDocument checkedModel) :=
  checkedInputFromFor checkedModel cells

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

private def checkedMixedResultFor? (model : FlatModel)
    (startField finishField storedField : FlatFieldDecl)
    (position : DateRangeConstructionPosition) (op : EqualityOp)
    (startRaw finishRaw : RawCell) (storedText : String) (storedRaw : RawCell) :
    Option DateRangeConstructionStoredComparisonResult := do
  let input ← checkedInputFromFor model [
    inputCell startField startRaw,
    inputCell finishField finishRaw,
    { address := { field := storedField.id, path := [] },
      stored := storedText, raw := storedRaw }]
  let operation ← (elaborateDateRangeConstructionStoredComparison model
    startField.id finishField.id storedField.id position op).toOption
  (operation.evaluate input).toOption

private def checkedFragmentResultFor? (model : FlatModel)
    (leftStartField leftFinishField rightStartField rightFinishField : FlatFieldDecl)
    (op : EqualityOp)
    (leftStartRaw leftFinishRaw rightStartRaw rightFinishRaw : RawCell) :
    Option DateRangeConstructionComparisonResult := do
  let input ← checkedInputFromFor model [
    inputCell leftStartField leftStartRaw,
    inputCell leftFinishField leftFinishRaw,
    inputCell rightStartField rightStartRaw,
    inputCell rightFinishField rightFinishRaw]
  let operation ← (elaborateDateRangeConstructionComparison model
    leftStartField.id leftFinishField.id rightStartField.id rightFinishField.id op).toOption
  (operation.evaluate input).toOption

private def checkedFragmentResult? := checkedFragmentResultFor? checkedModel

private def checkedYearFragmentResult? :=
  checkedFragmentResult?
    leftYearStart leftYearFinish rightYearStart rightYearFinish

private def checkedYearMonthFragmentResult? :=
  checkedFragmentResult?
    leftMonthStart leftMonthFinish rightMonthStart rightMonthFinish

private def checkedMonthOnlyFragmentResult? :=
  checkedFragmentResult?
    leftMonthOnlyStart leftMonthOnlyFinish rightMonthOnlyStart rightMonthOnlyFinish

private def checkedMonthDayFragmentResult? :=
  checkedFragmentResult?
    leftMonthDayStart leftMonthDayFinish rightMonthDayStart rightMonthDayFinish

private def checkedMonthOnlyFragmentResultFor? (model : FlatModel) :=
  checkedFragmentResultFor? model
    leftMonthOnlyStart leftMonthOnlyFinish rightMonthOnlyStart rightMonthOnlyFinish

private def checkedMonthDayFragmentResultFor? (model : FlatModel) :=
  checkedFragmentResultFor? model
    leftMonthDayStart leftMonthDayFinish rightMonthDayStart rightMonthDayFinish

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

private def yearValue (year : Int) : DateValue := {
  instant := { epochMillis := 0 }
  parts := { year, month := 1, day := 1 }
  basis := .storedGregorian }

private def yearMonthValue (year : Int) (month : Nat) : DateValue := {
  instant := { epochMillis := 0 }
  parts := { year, month, day := 1 }
  basis := .storedGregorian }

private def monthDayValue (year : Int) (month day : Nat) : DateValue := {
  instant := { epochMillis := 0 }
  parts := { year, month, day }
  basis := .storedGregorian }

private def monthDayEndpoint (month day : Nat) :
    DateRangeConstructionEndpointValue :=
  .monthDay { month, day }

private def berlinDateValue? (year : Int) (month day : Nat) : Option DateValue := do
  let instant ← ModelZone.concreteResolveLocal? "Europe/Berlin" year month day 0 0 0
  pure { instant, parts := { year, month, day }, basis := .storedGregorian }

/- Construction-versus-field equality and inequality are exact complements on the maintained full-Date source pair. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .left constructed storedSame = .fired .value ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .left constructed storedSame = .notFired := by
  native_decide

/- Exact `MM` endpoints take their missing year from the model, complete by range position, and ignore the parsed carrier's year and instant. -/
example : ((checkedMonthOnlyFragmentResult? .equal
    (dateRaw (yearMonthValue 1999 2)) (dateRaw (yearMonthValue 1999 2))
    (dateRaw (yearMonthValue 2001 2)) (dateRaw (yearMonthValue 2001 2))).map fun result =>
      (result.left.start, result.left.finish,
        result.right.start, result.right.finish, result.verdict)) =
    some (.value (.exact ((berlinDateValue? 2024 2 1).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 2 1).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
      .fired .value) := by
  native_decide

/- Exact `MM-dd` endpoints likewise resolve the authored label against the model Base Year rather than the incoming year. -/
example : ((checkedMonthDayFragmentResult? .equal
    (dateRaw (monthDayValue 2000 2 29)) (dateRaw (monthDayValue 2000 2 29))
    (dateRaw (monthDayValue 2000 2 29)) (dateRaw (monthDayValue 2000 2 29))).map fun result =>
      (result.left.start, result.left.finish,
        result.right.start, result.right.finish, result.verdict)) =
    some (.value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
      .fired .value) := by
  native_decide

/- A non-leap Base Year changes the `MM` finish and admits only a real `MM-dd` label in that configured year. -/
example :
    ((checkedMonthOnlyFragmentResultFor? checkedModel2023 .equal
      (dateRaw (yearMonthValue 2000 2)) (dateRaw (yearMonthValue 2000 2))
      (dateRaw (yearMonthValue 2004 2)) (dateRaw (yearMonthValue 2004 2))).map fun result =>
        (result.left.start, result.left.finish, result.verdict)) =
      some (.value (.exact ((berlinDateValue? 2023 2 1).get (by native_decide))),
        .value (.exact ((berlinDateValue? 2023 2 28).get (by native_decide))),
        .fired .value) ∧
    ((checkedMonthDayFragmentResultFor? checkedModel2023 .equal
      (dateRaw (monthDayValue 2000 2 28)) (dateRaw (monthDayValue 2000 2 28))
      (dateRaw (monthDayValue 2004 2 28)) (dateRaw (monthDayValue 2004 2 28))).map fun result =>
        (result.left.start, result.left.finish, result.verdict)) =
      some (.value (.exact ((berlinDateValue? 2023 2 28).get (by native_decide))),
        .value (.exact ((berlinDateValue? 2023 2 28).get (by native_decide))),
        .fired .value) := by
  native_decide

/- A label real in its incoming carrier but unreal in the configured Base Year is a structural endpoint fault, never normalized. -/
example :
  let unrealIn2023 := monthDayValue 2000 2 29
  (do
    let input ← checkedInputFromFor checkedModel2023 [
      inputCell leftMonthDayStart (dateRaw unrealIn2023),
      inputCell leftMonthDayFinish (dateRaw (monthDayValue 2000 2 28)),
      inputCell rightMonthDayStart (dateRaw (monthDayValue 2000 2 28)),
      inputCell rightMonthDayFinish (dateRaw (monthDayValue 2000 2 28))]
    let operation ← (elaborateDateRangeConstructionComparison checkedModel2023
      leftMonthDayStart.id leftMonthDayFinish.id
      rightMonthDayStart.id rightMonthDayFinish.id .equal).toOption
    pure (match operation.evaluate input with
      | .ok _ => none
      | .error error => some error)) =
    some (some (.endpointDateUnavailable leftMonthDayStart.id unrealIn2023)) := by
  native_decide

/- Yearless endpoint projection still rejects impossible decoded month and month/day components. -/
example :
  let unrealMonth := yearMonthValue 2000 13
  let unrealMonthDay := monthDayValue 2000 2 30
  (do
    let input ← checkedInputFromFor checkedModelNoBase [
      inputCell leftMonthOnlyStart (dateRaw unrealMonth),
      inputCell leftMonthOnlyFinish (dateRaw (yearMonthValue 2000 3)),
      inputCell rightMonthOnlyStart (dateRaw (yearMonthValue 2000 2)),
      inputCell rightMonthOnlyFinish (dateRaw (yearMonthValue 2000 3))]
    let operation ← (elaborateDateRangeConstructionComparison checkedModelNoBase
      leftMonthOnlyStart.id leftMonthOnlyFinish.id
      rightMonthOnlyStart.id rightMonthOnlyFinish.id .equal).toOption
    pure (match operation.evaluate input with
      | .ok _ => none
      | .error error => some error)) =
      some (some (.endpointDateUnavailable leftMonthOnlyStart.id unrealMonth)) ∧
    (do
      let input ← checkedInputFromFor checkedModelNoBase [
        inputCell leftMonthDayStart (dateRaw unrealMonthDay),
        inputCell leftMonthDayFinish (dateRaw (monthDayValue 2000 3 1)),
        inputCell rightMonthDayStart (dateRaw (monthDayValue 2000 2 28)),
        inputCell rightMonthDayFinish (dateRaw (monthDayValue 2000 3 1))]
      let operation ← (elaborateDateRangeConstructionComparison checkedModelNoBase
        leftMonthDayStart.id leftMonthDayFinish.id
        rightMonthDayStart.id rightMonthDayFinish.id .equal).toOption
      pure (match operation.evaluate input with
        | .ok _ => none
        | .error error => some error)) =
      some (some (.endpointDateUnavailable leftMonthDayStart.id unrealMonthDay)) := by
  native_decide

/- Checked mixed execution preserves authored side, both rich operands, exact finish comparison, and complementary equality. -/
example :
    ((checkedMixedResult? .left .equal
      (dateRaw startValue) (dateRaw finishValue)
      "01.06.2024-30.06.2024" (.parsed (.dateRange storedSameValue))).map fun result =>
        (result.position, result.construction.start,
          result.stored, result.verdict)) =
      some (.left, .value (.exact startValue),
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

/- A no-Base-Year `MM` construction compares directly with the matching stored component profile without manufacturing a year. -/
example :
    ((checkedMixedResultFor? checkedModelNoBase
      leftMonthOnlyStart leftMonthOnlyFinish storedMonthRange .left .equal
      (dateRaw (yearMonthValue 1999 2)) (dateRaw (yearMonthValue 2001 3))
      "02/03" (.parsed (.dateRange (.yearlessMonth 2 3)))).map fun result =>
        (result.position, result.construction.start, result.construction.finish,
          result.stored, result.verdict)) =
      some (.left, .value (.month 2), .value (.month 3),
        .value (.yearlessMonth 2 3), .fired .value) := by
  native_decide

/- The mixed compatibility gate preserves both exact stored presentations rather than keying admission on one lexical spelling. -/
example :
    ((checkedMixedResultFor? checkedModel
      leftStart leftFinish storedIsoRange .left .equal
      (dateRaw startValue) (dateRaw finishValue)
      "2024-06-01/2024-06-30"
      (.parsed (.dateRange storedSameValue))).map fun result =>
        (result.stored, result.verdict)) =
      some (.value (.exact storedSameValue), .fired .value) := by
  native_decide

/- Yearless `MM` comparison is symmetric in authored position and observes changes to either ordered endpoint. -/
example :
    (checkedMixedResultFor? checkedModelNoBase
      leftMonthOnlyStart leftMonthOnlyFinish storedMonthRange .right .notEqual
      (dateRaw (yearMonthValue 2004 2)) (dateRaw (yearMonthValue 2004 3))
      "02/04" (.parsed (.dateRange (.yearlessMonth 2 4)))).map
        (fun result => (result.position, result.verdict)) =
      some (.right, .fired .value) ∧
    (checkedMixedResultFor? checkedModelNoBase
      leftMonthOnlyStart leftMonthOnlyFinish storedMonthRange .left .equal
      (dateRaw (yearMonthValue 1999 2)) (dateRaw (yearMonthValue 1999 3))
      "01/03" (.parsed (.dateRange (.yearlessMonth 1 3)))).map
        (fun result => result.verdict) = some .notFired := by
  native_decide

/- No-Base-Year `MM-dd` retains both month/day endpoint labels and delegates equality through the same shared cell seam. -/
example :
    ((checkedMixedResultFor? checkedModelNoBase
      leftMonthDayStart leftMonthDayFinish storedMonthDayRange .right .equal
      (dateRaw (monthDayValue 1999 2 29)) (dateRaw (monthDayValue 2001 3 1))
      "02-29/03-01" (.parsed (.dateRange (.yearlessMonthDay
        { month := 2, day := 29 } { month := 3, day := 1 })))).map fun result =>
          (result.position, result.construction.start, result.construction.finish,
            result.stored, result.verdict)) =
      some (.right, .value (monthDayEndpoint 2 29),
        .value (monthDayEndpoint 3 1),
        .value (.yearlessMonthDay
          { month := 2, day := 29 } { month := 3, day := 1 }),
        .fired .value) ∧
    (checkedMixedResultFor? checkedModelNoBase
      leftMonthDayStart leftMonthDayFinish storedMonthDayRange .left .notEqual
      (dateRaw (monthDayValue 2000 2 28)) (dateRaw (monthDayValue 2000 3 1))
      "02-28/03-02" (.parsed (.dateRange (.yearlessMonthDay
        { month := 2, day := 28 } { month := 3, day := 2 })))).map
          (fun result => result.verdict) = some (.fired .value) := by
  native_decide

/- Yearless mixed execution preserves formal-before-empty classification and stored emptiness through its rich result. -/
example :
    ((checkedMixedResultFor? checkedModelNoBase
      leftMonthOnlyStart leftMonthOnlyFinish storedMonthRange .left .equal
      (.rejected .malformed) .presentEmpty "" .presentEmpty).map fun result =>
        (result.construction.start, result.construction.finish,
          result.stored, result.verdict)) =
      some (.unknown .malformed, .empty, .empty, .unknown) := by
  native_decide

/- Mixed execution compares reconstructed instants, not the construction input's incoming instant. -/
example :
  let alteredStart := { startValue with instant := { epochMillis := 1001 } }
  (checkedMixedResult? .left .equal
    (dateRaw alteredStart) (dateRaw finishValue)
    "01.06.2024-30.06.2024" (.parsed (.dateRange storedSameValue))).map
      (fun result => (result.construction.start, result.verdict)) =
    some (.value (.exact startValue), .fired .value) := by
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
    some (.value (.exact startValue), .value (.exact finishValue),
      .value (.exact startValue), .value (.exact finishValue), .fired .value) := by
  native_decide

/- A checked `yyyy` DateFragment construction completes its start to January 1 and its finish to December 31 before comparing exact instants. -/
example : ((checkedYearFragmentResult? .equal
    (dateRaw (yearValue 2024)) (dateRaw (yearValue 2025))
    (dateRaw (yearValue 2024)) (dateRaw (yearValue 2025))).map fun result =>
      (result.left.start, result.left.finish,
        result.right.start, result.right.finish, result.verdict)) =
    some (.value (.exact ((berlinDateValue? 2024 1 1).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2025 12 31).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2024 1 1).get (by native_decide))),
      .value (.exact ((berlinDateValue? 2025 12 31).get (by native_decide))),
      .fired .value) := by
  native_decide

/- Exact `yyyy-MM` endpoints complete the start to day 1 and the finish to the leap-aware month end before comparison. -/
example :
    ((checkedYearMonthFragmentResult? .equal
      (dateRaw (yearMonthValue 2024 2)) (dateRaw (yearMonthValue 2024 2))
      (dateRaw (yearMonthValue 2024 2)) (dateRaw (yearMonthValue 2024 2))).map fun result =>
        (result.left.start, result.left.finish,
          result.right.start, result.right.finish, result.verdict)) =
      some (.value (.exact ((berlinDateValue? 2024 2 1).get (by native_decide))),
        .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
        .value (.exact ((berlinDateValue? 2024 2 1).get (by native_decide))),
        .value (.exact ((berlinDateValue? 2024 2 29).get (by native_decide))),
        .fired .value) ∧
    ((checkedYearMonthFragmentResult? .equal
      (dateRaw (yearMonthValue 2023 2)) (dateRaw (yearMonthValue 2023 2))
      (dateRaw (yearMonthValue 2023 2)) (dateRaw (yearMonthValue 2023 2))).map fun result =>
        (result.left.finish, result.right.finish, result.verdict)) =
      some (.value (.exact ((berlinDateValue? 2023 2 28).get (by native_decide))),
        .value (.exact ((berlinDateValue? 2023 2 28).get (by native_decide))),
        .fired .value) := by
  native_decide

/- The bounded extension remains component-exact within each construction. -/
example :
    (match elaborateDateRangeConstruction checkedModel
        leftYearStart.id leftFinish.id with
      | .error (.componentMismatch .yearFragment (.full _)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstruction checkedModel
        leftYearStart.id leftMonthFinish.id with
      | .error (.componentMismatch .yearFragment .yearMonthFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstruction checkedModel
        leftMonthOnlyStart.id leftMonthFinish.id with
      | .error (.componentMismatch (.monthFragment 2024) .yearMonthFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstruction checkedModel
        leftMonthDayStart.id leftFinish.id with
      | .error (.componentMismatch (.monthDayFragment 2024) (.full _)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstruction checkedModel
        wrongModeMonthFragment.id wrongModeMonthFragment.id with
      | .error (.start (.unsupportedPolicy _ .dayOptional "yyyy-MM")) => true
      | _ => false) = true := by
  native_decide

/- Matching yearless fragment profiles remain admissible without inventing a Base Year. -/
example :
    (match elaborateDateRangeConstruction checkedModelNoBase
        leftMonthOnlyStart.id leftMonthOnlyFinish.id with
      | .ok _ => true
      | .error _ => false) = true ∧
    (match elaborateDateRangeConstruction checkedModelNoBase
        leftMonthDayStart.id leftMonthDayFinish.id with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

/- Yearless `MM` execution retains all four authored months and compares both ordered endpoints. -/
example :
    ((checkedMonthOnlyFragmentResultFor? checkedModelNoBase .equal
      (dateRaw (yearMonthValue 1999 2)) (dateRaw (yearMonthValue 1999 3))
      (dateRaw (yearMonthValue 2001 2)) (dateRaw (yearMonthValue 2001 3))).map fun result =>
        (result.left.start, result.left.finish,
          result.right.start, result.right.finish, result.verdict)) =
      some (.value (.month 2), .value (.month 3),
        .value (.month 2), .value (.month 3), .fired .value) ∧
    (checkedMonthOnlyFragmentResultFor? checkedModelNoBase .notEqual
      (dateRaw (yearMonthValue 1999 2)) (dateRaw (yearMonthValue 1999 3))
      (dateRaw (yearMonthValue 2001 1)) (dateRaw (yearMonthValue 2001 3))).map
        (·.verdict) = some (.fired .value) ∧
    (checkedMonthOnlyFragmentResultFor? checkedModelNoBase .notEqual
      (dateRaw (yearMonthValue 1999 2)) (dateRaw (yearMonthValue 1999 3))
      (dateRaw (yearMonthValue 2001 2)) (dateRaw (yearMonthValue 2001 4))).map
        (·.verdict) = some (.fired .value) := by
  native_decide

/- Yearless `MM-dd` execution retains both component pairs and separates start-only and finish-only changes. -/
example :
    ((checkedMonthDayFragmentResultFor? checkedModelNoBase .equal
      (dateRaw (monthDayValue 2000 2 29)) (dateRaw (monthDayValue 2000 3 1))
      (dateRaw (monthDayValue 2004 2 29)) (dateRaw (monthDayValue 2004 3 1))).map fun result =>
        (result.left.start, result.left.finish,
          result.right.start, result.right.finish, result.verdict)) =
      some (.value (monthDayEndpoint 2 29), .value (monthDayEndpoint 3 1),
        .value (monthDayEndpoint 2 29), .value (monthDayEndpoint 3 1),
        .fired .value) ∧
    (checkedMonthDayFragmentResultFor? checkedModelNoBase .notEqual
      (dateRaw (monthDayValue 2000 2 27)) (dateRaw (monthDayValue 2000 3 1))
      (dateRaw (monthDayValue 2004 2 28)) (dateRaw (monthDayValue 2004 3 1))).map
        (·.verdict) = some (.fired .value) ∧
    (checkedMonthDayFragmentResultFor? checkedModelNoBase .notEqual
      (dateRaw (monthDayValue 2000 2 28)) (dateRaw (monthDayValue 2000 3 2))
      (dateRaw (monthDayValue 2004 2 28)) (dateRaw (monthDayValue 2004 3 1))).map
        (·.verdict) = some (.fired .value) := by
  native_decide

/- Yearless execution keeps empty suppression and formal-before-empty precedence. -/
example :
    ((checkedMonthOnlyFragmentResultFor? checkedModelNoBase .equal
      .presentEmpty (dateRaw (yearMonthValue 1999 3))
      (dateRaw (yearMonthValue 2001 2)) (dateRaw (yearMonthValue 2001 3))).map fun result =>
        (result.left.start, result.verdict)) = some (.empty, .notFired) ∧
    ((checkedMonthDayFragmentResultFor? checkedModelNoBase .equal
      .presentEmpty (.rejected .malformed)
      (dateRaw (monthDayValue 2004 2 28)) (dateRaw (monthDayValue 2004 3 1))).map fun result =>
        (result.left.start, result.left.finish, result.verdict)) =
      some (.empty, .unknown .malformed, .unknown) := by
  native_decide

/- The no-Base-Year route still refuses component mismatch within and across constructions. -/
example :
    (match elaborateDateRangeConstruction checkedModelNoBase
        leftMonthOnlyStart.id leftMonthDayFinish.id with
      | .error (.componentMismatch .yearlessMonth .yearlessMonthDay) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionComparison checkedModelNoBase
        leftMonthOnlyStart.id leftMonthOnlyFinish.id
        rightMonthDayStart.id rightMonthDayFinish.id .equal with
      | .error (.componentMismatch .yearlessMonth .yearlessMonthDay) => true
      | _ => false) = true := by
  native_decide

/- Component compatibility is checked across both constructions, not only within each endpoint pair. -/
example :
    (match elaborateDateRangeConstructionComparison checkedModel
        leftYearStart.id leftYearFinish.id leftStart.id leftFinish.id .equal with
      | .error (.componentMismatch .yearFragment (.full _)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionComparison checkedModel
        leftStart.id leftFinish.id rightYearStart.id rightYearFinish.id .equal with
      | .error (.componentMismatch (.full _) .yearFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionComparison checkedModel
        leftYearStart.id leftYearFinish.id rightMonthStart.id rightMonthFinish.id .equal with
      | .error (.componentMismatch .yearFragment .yearMonthFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionComparison checkedModel
        leftMonthOnlyStart.id leftMonthOnlyFinish.id
        rightMonthStart.id rightMonthFinish.id .equal with
      | .error (.componentMismatch (.monthFragment 2024) .yearMonthFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionComparison checkedModel
        leftMonthDayStart.id leftMonthDayFinish.id
        rightStart.id rightFinish.id .equal with
      | .error (.componentMismatch (.monthDayFragment 2024) (.full _)) => true
      | _ => false) = true := by
  native_decide

/- Component identity, not lexical format spelling, admits the two complete Date profiles across constructions. -/
example :
    (match elaborateDateRangeConstructionComparison checkedModel
        leftStart.id leftFinish.id dottedStart.id dottedFinish.id .equal with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

/- Unsupported exact fragments remain excluded, while supported construction profiles must match the stored declaration's component identity. -/
example :
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftYearStart.id leftYearFinish.id storedRange.id .left .equal with
      | .error (.unsupportedConstructionProfile .yearFragment .yearFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftYearStart.id leftYearFinish.id storedRange.id .right .equal with
      | .error (.unsupportedConstructionProfile .yearFragment .yearFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftMonthStart.id leftMonthFinish.id storedRange.id .left .equal with
      | .error (.unsupportedConstructionProfile
          .yearMonthFragment .yearMonthFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftMonthOnlyStart.id leftMonthOnlyFinish.id storedRange.id .left .equal with
      | .error (.unsupportedConstructionProfile
          (.monthFragment 2024) (.monthFragment 2024)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftMonthDayStart.id leftMonthDayFinish.id storedRange.id .right .equal with
      | .error (.unsupportedConstructionProfile
          (.monthDayFragment 2024) (.monthDayFragment 2024)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModelNoBase
        leftMonthOnlyStart.id leftMonthOnlyFinish.id storedRange.id .left .equal with
      | .error (.componentMismatch .yearlessMonth (.exact .dayMonthYearDash)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModelNoBase
        leftMonthDayStart.id leftMonthDayFinish.id storedRange.id .right .equal with
      | .error (.componentMismatch .yearlessMonthDay (.exact .dayMonthYearDash)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModelNoBase
        leftMonthOnlyStart.id leftMonthOnlyFinish.id
        storedMonthDayRange.id .left .equal with
      | .error (.componentMismatch .yearlessMonth .yearlessMonthDay) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModelNoBase
        leftMonthDayStart.id leftMonthDayFinish.id storedMonthRange.id .right .equal with
      | .error (.componentMismatch .yearlessMonthDay .yearlessMonth) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftMonthOnlyStart.id leftMonthOnlyFinish.id storedMonthRange.id .left .equal with
      | .error (.unsupportedConstructionProfile
          (.monthFragment 2024) (.monthFragment 2024)) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftStart.id leftFinish.id storedMonthRange.id .right .equal with
      | .error (.componentMismatch (.full .yearMonthDayDashes)
          .yearlessMonth) => true
      | _ => false) = true := by
  native_decide

/- Full-profile refinement participates in authored static order before the later mixed operand is certified. -/
example :
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftYearStart.id leftYearFinish.id 99 .left .equal with
      | .error (.unsupportedConstructionProfile .yearFragment .yearFragment) => true
      | _ => false) = true ∧
    (match elaborateDateRangeConstructionStoredComparison checkedModel
        leftYearStart.id leftYearFinish.id 99 .right .equal with
      | .error (.stored (.source (.unknownFieldId 99))) => true
      | _ => false) = true := by
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
        some (.value (.exact startValue), .fired .value) := by
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

/- Pure construction classification retains computation poison and projects it to validation UNKNOWN even when the same construction also has an empty endpoint. -/
example :
    let left : DateRangeConstructionObservation := {
      start := .empty
      finish := .poison .computedDependency }
    let right : DateRangeConstructionObservation := {
      start := .value (.exact startValue)
      finish := .value (.exact finishValue) }
    left.finish = .poison .computedDependency ∧
      EqualityOp.equal.evalDateRangeCellValues
        left.comparisonOperand right.comparisonOperand = .unknown := by
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
