import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime
import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Temporal

/-! # Ordinary repeatable temporal whole-rule locks -/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryTemporal

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def checkedDateRawAt
    (epochMillis year : Int) (month day : Nat) : RawCell :=
  .parsed (.temporal (.date { epochMillis }
    { year, month, day } .storedGregorian))

private def checkedDateRaw (year : Int) (month day : Nat) : RawCell :=
  checkedDateRawAt 0 year month day

private def checkedDateTimeRawAtTime
    (epochMillis year : Int) (month day : Nat) (time : TimeOfDay) : RawCell :=
  .parsed (.temporal (.dateTime { epochMillis }
    { year, month, day } time
    .storedGregorian))

private def midnight : TimeOfDay :=
  (TimeOfDay.ofHms? 0 0 0).get (by native_decide)

private def fiveThirtyFifteen : TimeOfDay :=
  (TimeOfDay.ofHms? 5 30 15).get (by native_decide)

private def checkedDateTimeRawAt
    (epochMillis year : Int) (month day : Nat) : RawCell :=
  checkedDateTimeRawAtTime epochMillis year month day midnight

private def repeatableDateDifferenceData
    (leftStored : String) (leftRaw : Option RawCell)
    (rightStored : String) (rightRaw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells :=
      leftRaw.toList.map (fun cell => {
        address := { field := innerDate.id, path := [1, 1] }
        stored := leftStored
        raw := cell }) ++
      rightRaw.toList.map (fun cell => {
        address := { field := innerEarlierDate.id, path := [1, 1] }
        stored := rightStored
        raw := cell }) }

private def nestedDateDifferenceData
    (outerStored : String) (outerRaw : Option RawCell)
    (innerStored : String) (innerRaw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells :=
      outerRaw.toList.map (fun cell => {
        address := { field := outerDate.id, path := [1] }
        stored := outerStored
        raw := cell }) ++
      innerRaw.toList.map (fun cell => {
        address := { field := innerDate.id, path := [1, 1] }
        stored := innerStored
        raw := cell }) }

private def repeatableDayDifferenceData
    (dateStored : String) (dateRaw : Option RawCell)
    (dateTimeStored : String) (dateTimeRaw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells :=
      dateRaw.toList.map (fun cell => {
        address := { field := innerDate.id, path := [1, 1] }
        stored := dateStored
        raw := cell }) ++
      dateTimeRaw.toList.map (fun cell => {
        address := { field := innerDateTime.id, path := [1, 1] }
        stored := dateTimeStored
        raw := cell }) }

private def repeatableDateTimeDifferenceData
    (leftStored : String) (leftRaw : Option RawCell)
    (rightStored : String) (rightRaw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells :=
      leftRaw.toList.map (fun cell => {
        address := { field := innerDateTime.id, path := [1, 1] }
        stored := leftStored
        raw := cell }) ++
      rightRaw.toList.map (fun cell => {
        address := { field := innerEarlierDateTime.id, path := [1, 1] }
        stored := rightStored
        raw := cell }) }

private def dateDifferenceRuleSnapshot?
    (rule : Option (CheckedResolvedValidationRule ordinaryIterationModel))
    (data : DocumentData) :
    Option (Option (List RepeatableLevel) × Bool × List (Env × Verdict)) := do
  let checked ← rule
  let outcomes ← evalOrdinaryRule? checked data
  pure (checked.iterationScope, checked.requiresAddressedValidation,
    outcomes.map fun entry => (entry.1, entry.2.verdict))

private def repeatableDateDifferenceSnapshot?
    (unit : DateDifferenceUnit) (left right : String)
    (op : NumericValidationOp) (expected : Rat)
    (data : DocumentData) :
    Option (Option (List RepeatableLevel) × Bool × List (Env × Verdict)) :=
  dateDifferenceRuleSnapshot?
    (repeatableDateDifferenceRule? unit left right op expected) data

private def dateDifferenceStructuralFailure?
    (rule : Option (CheckedResolvedValidationRule ordinaryIterationModel))
    (data : DocumentData) (outer : Env) :
    Option CheckedAddressingError := do
  let checked ← rule
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer
    input := .checked document
  }
  match checked.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def repeatableDateDifferenceStructuralFailure? :
    Option CheckedAddressingError :=
  dateDifferenceStructuralFailure?
    (repeatableDateDifferenceRule? .months
      "InnerDate" "InnerEarlierDate" (.ordinary .equal) (-17))
    (repeatableDateDifferenceData "2024-06-25"
      (some (checkedDateRaw 2024 6 25)) "2023-01-25"
      (some (checkedDateRaw 2023 1 25))) []

private def repeatableDateDifferenceConsumerSnapshot? :
    Option (List String × List String × List RepeatableLevel ×
      DateDifferenceUnit × CellAddr × Option String × CellAddr × Option String ×
      Verdict) := do
  let leftDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerDate.id).toOption
  let rightDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerEarlierDate.id).toOption
  let data := repeatableDateDifferenceData "2024-06-25"
    (some (checkedDateRaw 2024 6 25)) "2023-01-25"
    (some (checkedDateRaw 2023 1 25))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let left ←
    (document.addressedCell [(10, 1), (20, 1)] innerDate.id).toOption
  let right ←
    (document.addressedCell [(10, 1), (20, 1)]
      innerEarlierDate.id).toOption
  let rule ← repeatableDateDifferenceRule? .months
    "InnerDate" "InnerEarlierDate" (.ordinary .equal) (-17)
  let outcomes ← evalOrdinaryRule? rule data
  let outcome ← outcomes.head?
  pure (leftDeclaration.path, rightDeclaration.path,
    leftDeclaration.repeatableScope, .months,
    left.address, left.stored, right.address, right.stored, outcome.2.verdict)

private def nestedDateDifferenceConsumerSnapshot? :
    Option (List RepeatableLevel × List RepeatableLevel ×
      CellAddr × CellAddr × Verdict) := do
  let outerDeclaration ←
    (ordinaryIterationModel.lookupUniqueId outerDate.id).toOption
  let innerDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerDate.id).toOption
  let data := nestedDateDifferenceData "2024-06-25"
    (some (checkedDateRaw 2024 6 25)) "2023-01-25"
    (some (checkedDateRaw 2023 1 25))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outer ← (document.addressedCell [(10, 1)] outerDate.id).toOption
  let inner ←
    (document.addressedCell [(10, 1), (20, 1)] innerDate.id).toOption
  let rule := repeatableDateDifferenceRuleWith? .months
    (.field (ordinaryPath ["Order", "Sections"] "OuterDate"))
    (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
    (.ordinary .equal) (-17)
  let checked ← rule
  let outcomes ← evalOrdinaryRule? checked data
  let outcome ← outcomes.head?
  pure (outerDeclaration.repeatableScope, innerDeclaration.repeatableScope,
    outer.address, inner.address, outcome.2.verdict)

private def repeatableDayDifferenceConsumerSnapshot? :
    Option (ModelZone.ConcreteProfile × TemporalKind × TemporalKind ×
      CellAddr × CellAddr × Verdict) := do
  let dateDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerDate.id).toOption
  let dateTimeDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerDateTime.id).toOption
  let date ← dateDeclaration.toTemporalField?
  let dateTime ← dateTimeDeclaration.toTemporalField?
  let data := repeatableDayDifferenceData "2024-06-25"
    (some (checkedDateRawAt 0 2024 6 25)) "2024-06-26T00:00:00"
    (some (checkedDateTimeRawAt 86400000 2024 6 26))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let left ←
    (document.addressedCell [(10, 1), (20, 1)] innerDate.id).toOption
  let right ←
    (document.addressedCell [(10, 1), (20, 1)]
      innerDateTime.id).toOption
  let rule ← repeatableDayDifferenceRule?
    (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
    (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
    (.ordinary .equal) 1
  let outcomes ← evalOrdinaryRule? rule data
  let outcome ← outcomes.head?
  pure (.utc, date.kind, dateTime.kind,
    left.address, right.address, outcome.2.verdict)

private def repeatableDateTimeDifferenceSnapshot?
    (unit : DateTimeDifferenceUnit) (op : NumericValidationOp)
    (expected : Rat) (reverse : Bool) (data : DocumentData) :
    Option (Option (List RepeatableLevel) × Bool × List (Env × Verdict)) :=
  let left : SurfaceDateDifferenceOperand :=
    .field (ordinaryPath ["Order", "Sections", "Items"]
      (if reverse then "InnerEarlierDateTime" else "InnerDateTime"))
  let right : SurfaceDateDifferenceOperand :=
    .field (ordinaryPath ["Order", "Sections", "Items"]
      (if reverse then "InnerDateTime" else "InnerEarlierDateTime"))
  dateDifferenceRuleSnapshot?
    (repeatableDateTimeDifferenceRule? unit left right op expected) data

private def repeatableDateTimeDifferenceConsumerSnapshot? :
    Option (DateTimeDifferenceUnit × FlatTemporalField × FlatTemporalField ×
      CellAddr × Option String × CellAddr × Option String × Verdict) := do
  let leftDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerDateTime.id).toOption
  let rightDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerEarlierDateTime.id).toOption
  let leftField ← leftDeclaration.toTemporalField?
  let rightField ← rightDeclaration.toTemporalField?
  let data := repeatableDateTimeDifferenceData
    "2024-06-25T05:30:15"
    (some (checkedDateTimeRawAtTime 19815000 2024 6 25 fiveThirtyFifteen))
    "2024-06-25T00:00:00"
    (some (checkedDateTimeRawAtTime 0 2024 6 25 midnight))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let left ←
    (document.addressedCell [(10, 1), (20, 1)]
      innerDateTime.id).toOption
  let right ←
    (document.addressedCell [(10, 1), (20, 1)]
      innerEarlierDateTime.id).toOption
  let rule ← repeatableDateTimeDifferenceRule? .hours
    (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
    (.field
      (ordinaryPath ["Order", "Sections", "Items"] "InnerEarlierDateTime"))
    (.ordinary .equal) (-5)
  let outcomes ← evalOrdinaryRule? rule data
  let outcome ← outcomes.head?
  pure (.hours, leftField, rightField, left.address, left.stored,
    right.address, right.stored, outcome.2.verdict)

private def expectedRepeatableDateDifference
    (verdict : Verdict) :
    Option (Option (List RepeatableLevel) × Bool × List (Env × Verdict)) :=
  some (some [10, 20], true, [([(10, 1), (20, 1)], verdict)])

/- One addressed ordinary atom now reads two Date operands in authored order. Missing input keeps the symmetric-zero omission account, formal invalidity remains UNKNOWN, and an incomplete structural environment cannot become UNKNOWN. -/
example :
    (repeatableDateDifferenceSnapshot? .months
      "InnerDate" "InnerEarlierDate" (.ordinary .equal) (-17)
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateDifferenceSnapshot? .months
      "InnerEarlierDate" "InnerDate" (.ordinary .equal) 17
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateDifferenceSnapshot? .months
      "InnerDate" "InnerEarlierDate" (.ordinary .less) 1
      (repeatableDateDifferenceData "" none "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .omission)) = true ∧
    (repeatableDateDifferenceSnapshot? .years
      "InnerDate" "InnerEarlierDate" (.ordinary .equal) 1
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "bad"
        (some (.rejected .malformed))) ==
      expectedRepeatableDateDifference .unknown) = true ∧
    repeatableDateDifferenceStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

/- Addressed calendar-day difference retains exact instants and decoded Date/DateTime labels under the checked UTC profile. Operand order, Base Year, missing/formal polarity, and structural failure reuse the established two-field boundary. -/
example :
    let date : SurfaceDateDifferenceOperand :=
      .field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate")
    let dateTime : SurfaceDateDifferenceOperand :=
      .field (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime")
    let data := repeatableDayDifferenceData "2024-06-25"
      (some (checkedDateRawAt 0 2024 6 25)) "2024-06-26T00:00:00"
      (some (checkedDateTimeRawAt 86400000 2024 6 26))
    (dateDifferenceRuleSnapshot?
      (repeatableDayDifferenceRule? date dateTime (.ordinary .equal) 1)
      data == expectedRepeatableDateDifference (.fired .value)) = true ∧
    (dateDifferenceRuleSnapshot?
      (repeatableDayDifferenceRule? dateTime date (.ordinary .equal) (-1))
      data == expectedRepeatableDateDifference (.fired .value)) = true ∧
    (dateDifferenceRuleSnapshot?
      (repeatableDayDifferenceRule? date dateTime (.ordinary .less) 2)
      (repeatableDayDifferenceData "" none "2024-06-26T00:00:00"
        (some (checkedDateTimeRawAt 86400000 2024 6 26))) ==
      expectedRepeatableDateDifference (.fired .omission)) = true ∧
    (dateDifferenceRuleSnapshot?
      (repeatableDayDifferenceRule? date dateTime (.ordinary .equal) 1)
      (repeatableDayDifferenceData "2024-06-25"
        (some (checkedDateRawAt 0 2024 6 25)) "bad"
        (some (.rejected .malformed))) ==
      expectedRepeatableDateDifference .unknown) = true ∧
    (dateDifferenceRuleSnapshot?
      (repeatableDayDifferenceRule? (.baseYear .direct) date
        (.ordinary .equal) 366)
      (repeatableDayDifferenceData "2021-01-01"
        (some (checkedDateRawAt 1609459200000 2021 1 1)) "" none) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    dateDifferenceStructuralFailure?
      (repeatableDayDifferenceRule? date dateTime (.ordinary .equal) 1)
      data [] = some (.environment (.missingBinding 10)) := by
  native_decide

/- Addressed sub-day differences reuse the exact-instant core in authored order. Each unit truncates independently, negative hours truncate toward zero, missing is symmetric omission-typed zero, formal invalidity remains UNKNOWN, and incomplete addressing remains structural. -/
example :
    let data := repeatableDateTimeDifferenceData
      "2024-06-25T05:30:15"
      (some (checkedDateTimeRawAtTime 19815000 2024 6 25 fiveThirtyFifteen))
      "2024-06-25T00:00:00"
      (some (checkedDateTimeRawAtTime 0 2024 6 25 midnight))
    (repeatableDateTimeDifferenceSnapshot? .hours
      (.ordinary .equal) (-5) false data ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateTimeDifferenceSnapshot? .hours
      (.ordinary .equal) 5 true data ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateTimeDifferenceSnapshot? .minutes
      (.ordinary .equal) (-330) false data ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateTimeDifferenceSnapshot? .seconds
      (.ordinary .equal) (-19815) false data ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateTimeDifferenceSnapshot? .minutes
      (.ordinary .less) 1 false
      (repeatableDateTimeDifferenceData ""
        none "2024-06-25T00:00:00"
        (some (checkedDateTimeRawAtTime 0 2024 6 25 midnight))) ==
      expectedRepeatableDateDifference (.fired .omission)) = true ∧
    (repeatableDateTimeDifferenceSnapshot? .seconds
      (.ordinary .equal) 1 false
      (repeatableDateTimeDifferenceData "bad"
        (some (.rejected .malformed)) "2024-06-25T00:00:00"
        (some (checkedDateTimeRawAtTime 0 2024 6 25 midnight))) ==
      expectedRepeatableDateDifference .unknown) = true ∧
    dateDifferenceStructuralFailure?
      (repeatableDateTimeDifferenceRule? .hours
        (.field
          (ordinaryPath ["Order", "Sections", "Items"] "InnerDateTime"))
        (.field
          (ordinaryPath ["Order", "Sections", "Items"]
            "InnerEarlierDateTime"))
        (.ordinary .equal) (-5))
      data [] = some (.environment (.missingBinding 10)) := by
  native_decide

/- The generalized ordinary resolver projects compatible ancestor/current operands from one complete environment; a Base-Year operand leaves the field scope unchanged. -/
example :
    (dateDifferenceRuleSnapshot?
      (repeatableDateDifferenceRuleWith? .months
        (.field (ordinaryPath ["Order", "Sections"] "OuterDate"))
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.ordinary .equal) (-17))
      (nestedDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (dateDifferenceRuleSnapshot?
      (repeatableDateDifferenceRuleWith? .years
        (.baseYear .direct)
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.ordinary .equal) 1)
      (nestedDateDifferenceData "" none "2021-06-25"
        (some (checkedDateRaw 2021 6 25))) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (dateDifferenceRuleSnapshot?
      (repeatableDateDifferenceRuleWith? .years
        (.baseYear .direct)
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.ordinary .less) 1)
      (nestedDateDifferenceData "" none "" none) ==
      expectedRepeatableDateDifference (.fired .omission)) = true ∧
    dateDifferenceStructuralFailure?
      (repeatableDateDifferenceRuleWith? .months
        (.field (ordinaryPath ["Order", "Sections"] "OuterDate"))
        (.field (ordinaryPath ["Order", "Sections", "Items"] "InnerDate"))
        (.ordinary .equal) (-17))
      (nestedDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) [(10, 1)] =
      some (.environment (.missingBinding 20)) := by
  native_decide

/- Execute, Transform, and Explain can recover both ordered model certificates, both checked addresses and stored payloads, the selected period unit, and the same verdict. -/
example :
    (repeatableDateDifferenceConsumerSnapshot? ==
      some (
        ["Order", "Sections", "Items", "InnerDate"],
        ["Order", "Sections", "Items", "InnerEarlierDate"],
        [10, 20],
        .months,
        { field := innerDate.id, path := [1, 1] },
        some "2024-06-25",
        { field := innerEarlierDate.id, path := [1, 1] },
        some "2023-01-25",
        .fired .value)) = true := by
  native_decide

/- The nested consumer view retains distinct ancestor/current declaration scopes and exact addresses beside the same Execute verdict. -/
example :
    nestedDateDifferenceConsumerSnapshot? =
      some (
        [10],
        [10, 20],
        { field := outerDate.id, path := [1] },
        { field := innerDate.id, path := [1, 1] },
        .fired .value) := by
  native_decide

/- The calendar-day consumer view retains the concrete profile, both temporal kinds, both checked addresses, and the Execute verdict without re-resolving either instant. -/
example :
    repeatableDayDifferenceConsumerSnapshot? =
      some (
        .utc,
        .date,
        .dateTime,
        { field := innerDate.id, path := [1, 1] },
        { field := innerDateTime.id, path := [1, 1] },
        .fired .value) := by
  native_decide

/- Execute, Transform, and Explain recover the elapsed unit, ordered DateTime certificates, checked addresses and payloads, and the same result without flattening either source or re-resolving an instant. -/
example :
    (repeatableDateTimeDifferenceConsumerSnapshot? ==
      some (
        .hours,
        { id := innerDateTime.id, kind := .dateTime,
          components := dateTimeComponents },
        { id := innerEarlierDateTime.id, kind := .dateTime,
          components := dateTimeComponents },
        { field := innerDateTime.id, path := [1, 1] },
        some "2024-06-25T05:30:15",
        { field := innerEarlierDateTime.id, path := [1, 1] },
        some "2024-06-25T00:00:00",
        .fired .value)) = true := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryTemporal
