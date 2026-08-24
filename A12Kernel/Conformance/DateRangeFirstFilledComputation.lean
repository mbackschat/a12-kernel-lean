import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Semantics.TemporalApplication

/-! # Bounded DateRange `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.DateRangeFirstFilledComputation

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd")
    (separator : String := "/")
    (interpretationOfYear : Option DateRangeYearInterpretation := none) :
    FlatFieldDecl := {
  id
  groupPath
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator, interpretationOfYear }
  repeatableScope := scope
}

private def target := rangeField 1 ["Cart"] "FirstWindow"
private def source := rangeField 2 ["Cart", "Lines"] "Window" [10]
private def otherFormatSource :=
  rangeField 3 ["Cart", "Lines"] "DottedWindow" [10] "dd.MM.yyyy" "-"
private def otherSeparatorTarget :=
  rangeField 4 ["Cart"] "MonthEmptyWindow" [] "MM" ""
private def otherSeparatorSource :=
  rangeField 5 ["Cart", "Lines"] "MonthEmptySource" [10] "MM" ""
private def dottedTarget :=
  rangeField 6 ["Cart"] "DottedTarget" [] "dd.MM.yyyy" "-"
private def dottedSource :=
  rangeField 7 ["Cart", "Lines"] "DottedSource" [10] "dd.MM.yyyy" "-"
private def dayMonthDottedTarget :=
  rangeField 8 ["Cart"] "DayMonthDottedTarget" [] "dd.MM" "-"
private def dayMonthDottedSource :=
  rangeField 9 ["Cart", "Lines"] "DayMonthDottedSource" [10]
    "dd.MM" "-"
private def yearTarget :=
  rangeField 10 ["Cart"] "YearTarget" [] "yyyy" "/"
private def yearSource :=
  rangeField 11 ["Cart", "Lines"] "YearSource" [10] "yyyy" "/"
private def yearMonthTarget :=
  rangeField 12 ["Cart"] "YearMonthTarget" [] "yyyy-MM" "/"
private def yearMonthSource :=
  rangeField 13 ["Cart", "Lines"] "YearMonthSource" [10] "yyyy-MM" "/"
private def monthTarget :=
  rangeField 14 ["Cart"] "MonthTarget" [] "MM" "/"
private def monthSource :=
  rangeField 15 ["Cart", "Lines"] "MonthSource" [10] "MM" "/"
private def monthDayTarget :=
  rangeField 16 ["Cart"] "MonthDayTarget" [] "MM-dd" "/"
private def monthDaySource :=
  rangeField 17 ["Cart", "Lines"] "MonthDaySource" [10] "MM-dd" "/"
private def fromTarget :=
  rangeField 18 ["Cart"] "FromTarget" [] "dd.MM" "-" (some .anchorStart)
private def fromSource :=
  rangeField 19 ["Cart", "Lines"] "FromSource" [10] "dd.MM" "-"
    (some .anchorStart)
private def toTarget :=
  rangeField 20 ["Cart"] "ToTarget" [] "dd.MM" "-" (some .anchorFinish)
private def toSource :=
  rangeField 21 ["Cart", "Lines"] "ToSource" [10] "dd.MM" "-"
    (some .anchorFinish)
private def model : FlatModel := {
  fields := [target, source, otherFormatSource, otherSeparatorTarget,
    otherSeparatorSource, dottedTarget, dottedSource, dayMonthDottedTarget,
    dayMonthDottedSource, yearTarget, yearSource, yearMonthTarget,
    yearMonthSource, monthTarget, monthSource, monthDayTarget, monthDaySource,
    fromTarget, fromSource, toTarget, toSource]
  repeatableGroups := [
    { level := 10, path := ["Cart", "Lines"], repeatability := some 99 }]
  timeZoneId := "UTC"
}

private def configuredModel : FlatModel := { model with baseYear := some 2024 }
private def interpretationModel : FlatModel := { model with baseYear := some 2020 }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Cart" }, { name := "Lines", starred := true }]
  field
}

private def checkedFor? (candidate : FlatModel)
    (targetField : FieldId) (field : String) :=
  (checkDateRangeFirstFilledComputation
    candidate ["Cart"] targetField (star field)).toOption

private def checked? := checkedFor? model

private def preparedFor? (candidate : FlatModel) :
    Option (PreparedFlatStringContext candidate builtinStringPatternCompiler) :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler candidate).toOption

private def dateValue (epochMillis : Int) (year month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def rangeValue (startMillis finishMillis : Int)
    (startDay finishDay : Nat) : DateRangeValue := {
  start := dateValue startMillis 2024 3 startDay
  finish := dateValue finishMillis 2024 3 finishDay
}

private structure SourceInput where
  row : Nat
  stored : String
  raw : RawCell

private def inputFor? (candidate : FlatModel) (sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option (CheckedDocument candidate) := do
  let prepared ← preparedFor? candidate
  let sourceCells := sourceInputs.map fun input => {
    address := { field := sourceDeclaration.id, path := [input.row] }
    stored := input.stored
    raw := input.raw
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] }]
    cells := sourceCells
  }).toOption

private def executionFor? (candidate : FlatModel)
    (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option (Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome) := do
  let operation ← checkedFor? candidate targetDeclaration.id sourceDeclaration.name
  let input ← inputFor? candidate sourceDeclaration sourceInputs
  pure (operation.execute input)

private def execution? := executionFor? model target source

private def signatureForModel? (candidate : FlatModel)
    (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) : Option String := do
  let execution ← executionFor? candidate targetDeclaration sourceDeclaration sourceInputs
  let outcome ← execution.toOption
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .errored stored _ => "ERRORED|" ++ stored.text
    | .poison _ => "POISON")

private def signatureFor? := signatureForModel? model
private def signature? := signatureFor? target source

private def selectedRange := rangeValue 1710892800000 1710979200000 20 21

private def exactRange (startMillis finishMillis : Int)
    (startYear startMonth startDay finishYear finishMonth finishDay : Nat) :
    DateRangeCellValue := .exact {
  start := dateValue startMillis startYear startMonth startDay
  finish := dateValue finishMillis finishYear finishMonth finishDay
}

/- The retained temporal-family probe Kernel-calibrates these exact all-empty and first-row-filled result signatures. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [{
        row := 1
        stored := "2024-03-20/2024-03-21"
        raw := .parsed (.dateRange selectedRange)
      }] = some "VALUE|2024-03-20/2024-03-21" := by
  native_decide

/- A declared year interpretation is not part of direct-star carrier admission, so opposite interpretations cross in either direction. -/
example :
    (checkedFor? interpretationModel fromTarget.id "ToSource").isSome = true ∧
      (checkedFor? interpretationModel toTarget.id "FromSource").isSome = true := by
  native_decide

/- The selected exact range retains its source-side endpoint years while the target stores its own yearless spelling; an empty first row reaches the second and exhaustion clears. -/
example :
    signatureForModel? interpretationModel fromTarget toSource [{
      row := 1
      stored := "01.11-28.02"
      raw := .parsed (.dateRange (exactRange
        1572566400000 1582848000000 2019 11 1 2020 2 28))
    }] = some "VALUE|01.11-28.02" ∧
      signatureForModel? interpretationModel toTarget fromSource [{
        row := 1
        stored := "01.11-28.02"
        raw := .parsed (.dateRange (exactRange
          1604188800000 1614470400000 2020 11 1 2021 2 28))
      }] = some "VALUE|01.11-28.02" ∧
      signatureForModel? interpretationModel fromTarget toSource [{
        row := 2
        stored := "01.11-28.02"
        raw := .parsed (.dateRange (exactRange
          1572566400000 1582848000000 2019 11 1 2020 2 28))
      }] = some "VALUE|01.11-28.02" ∧
      signatureForModel? interpretationModel fromTarget toSource [] =
        some "CLEARED" ∧
      signatureForModel? interpretationModel toTarget fromSource [] =
        some "CLEARED" := by
  native_decide

/- All four fragment policies are admitted only as matching target/source pairs. -/
example :
    (checked? yearTarget.id "YearSource").isSome = true ∧
      (checked? yearMonthTarget.id "YearMonthSource").isSome = true ∧
      (checked? monthTarget.id "MonthSource").isSome = true ∧
      (checked? monthDayTarget.id "MonthDaySource").isSome = true ∧
      (checked? yearTarget.id "YearMonthSource").isNone = true ∧
      (checked? monthTarget.id "MonthDaySource").isNone = true := by
  native_decide

/- Year-bearing fragment sources retain typed endpoint identity and render through the matching target policy. -/
example :
    signatureFor? yearTarget yearSource [{
      row := 1
      stored := "2024/2025"
      raw := .parsed (.dateRange
        (exactRange 1704067200000 1767139200000 2024 1 1 2025 12 31))
    }] = some "VALUE|2024/2025" ∧
      signatureFor? yearMonthTarget yearMonthSource [{
        row := 1
        stored := "2024-12/2025-02"
        raw := .parsed (.dateRange
          (exactRange 1733011200000 1740700800000 2024 12 1 2025 2 28))
      }] = some "VALUE|2024-12/2025-02" := by
  native_decide

/- Without Base Year the checked cell preserves month and month/day component ranges rather than manufacturing exact dates. -/
example :
    signatureFor? monthTarget monthSource [{
      row := 1, stored := "", raw := .presentEmpty
    }, {
      row := 2
      stored := "01/02"
      raw := .parsed (.dateRange (.yearlessMonth 1 2))
    }] = some "VALUE|01/02" ∧
      signatureFor? monthDayTarget monthDaySource [{
        row := 1
        stored := "01-31/02-29"
        raw := .parsed (.dateRange (.yearlessMonthDay
          { month := 1, day := 31 } { month := 2, day := 29 }))
      }] = some "VALUE|01-31/02-29" := by
  native_decide

/- With Base Year the same month policy selects the resolved exact carrier but renders only its declared components. -/
example :
    signatureForModel? configuredModel monthTarget monthSource [{
      row := 1
      stored := "01/02"
      raw := .parsed (.dateRange
        (exactRange 1704067200000 1709164800000 2024 1 1 2024 2 29))
    }] = some "VALUE|01/02" ∧
      signatureForModel? configuredModel monthDayTarget monthDaySource [{
        row := 1
        stored := "01-31/02-29"
        raw := .parsed (.dateRange
          (exactRange 1706659200000 1709164800000 2024 1 31 2024 2 29))
      }] = some "VALUE|01-31/02-29" := by
  native_decide

/- The second exact legal declaration pair selects and renders the same checked typed endpoint payload. The complete profile computation checkpoint establishes this direct `FirstFilledValue` composition externally. -/
example :
    signatureFor? dottedTarget dottedSource [{
      row := 1
      stored := "20.03.2024-21.03.2024"
      raw := .parsed (.dateRange selectedRange)
    }] = some "VALUE|20.03.2024-21.03.2024" := by
  native_decide

/- A reached formal cause terminates before a later present range. -/
example :
    signature? [
      { row := 1, stored := "XX", raw := .rejected .dateRangeSeparator },
      {
        row := 2
        stored := "2024-03-20/2024-03-21"
        raw := .parsed (.dateRange selectedRange)
      }
    ] = some "POISON" := by
  native_decide

/- Source and target must expose the same declared component set, not the same lexical profile. Every crossing within a component set is admitted in both directions, including the two full-Date profiles, the two month-only separators, and the two day-and-month spellings. -/
example :
    (checked? target.id "Window").isSome = true ∧
      (checked? target.id "DottedWindow").isSome = true ∧
      (checked? dottedTarget.id "Window").isSome = true ∧
      (checked? dottedTarget.id "DottedSource").isSome = true ∧
      (checked? monthTarget.id "MonthEmptySource").isSome = true ∧
      (checked? otherSeparatorTarget.id "MonthSource").isSome = true ∧
      (checked? otherSeparatorTarget.id "MonthEmptySource").isSome = true ∧
      (checked? dayMonthDottedTarget.id "DayMonthDottedSource").isSome = true ∧
      (checked? monthDayTarget.id "DayMonthDottedSource").isSome = true ∧
      (checked? dayMonthDottedTarget.id "MonthDaySource").isSome = true := by
  native_decide

/- A different component set stays refused in either direction, so the relaxation is component-set equality rather than blanket DateRange assignability. -/
example :
    (checked? monthTarget.id "MonthDaySource").isNone = true ∧
      (checked? monthDayTarget.id "MonthSource").isNone = true ∧
      (checked? yearTarget.id "YearMonthSource").isNone = true ∧
      (checked? target.id "MonthSource").isNone = true ∧
      (checked? otherSeparatorTarget.id "DayMonthDottedSource").isNone = true := by
  native_decide

/- On a crossing the target's declared spelling decides the stored text, which a source-keyed renderer would get wrong on every row: the same component pair stores `0609` under the empty separator and `06/09` under slash, and one full-Date instant pair stores both lexical forms. -/
example :
    signatureFor? otherSeparatorTarget monthSource [{
      row := 1
      stored := "06/09"
      raw := .parsed (.dateRange (.yearlessMonth 6 9))
    }] = some "VALUE|0609" ∧
      signatureFor? monthTarget otherSeparatorSource [{
        row := 1
        stored := "0609"
        raw := .parsed (.dateRange (.yearlessMonth 6 9))
      }] = some "VALUE|06/09" ∧
      signatureFor? target dottedSource [{
        row := 1
        stored := "01.06.2024-30.06.2024"
        raw := .parsed (.dateRange
          (exactRange 1717200000000 1719705600000 2024 6 1 2024 6 30))
      }] = some "VALUE|2024-06-01/2024-06-30" ∧
      signatureFor? dottedTarget source [{
        row := 1
        stored := "2024-06-01/2024-06-30"
        raw := .parsed (.dateRange
          (exactRange 1717200000000 1719705600000 2024 6 1 2024 6 30))
      }] = some "VALUE|01.06.2024-30.06.2024" := by
  native_decide

/- Each lexical presentation stores its target's own spelling: the empty separator concatenates the two months and the dotted pair spells day before month. A shared-component sibling would have stored `06/09` and `06-01/09-30`. -/
example :
    signatureFor? otherSeparatorTarget otherSeparatorSource [{
      row := 1, stored := "", raw := .presentEmpty
    }, {
      row := 2
      stored := "0609"
      raw := .parsed (.dateRange (.yearlessMonth 6 9))
    }] = some "VALUE|0609" ∧
      signatureFor? dayMonthDottedTarget dayMonthDottedSource [{
        row := 1
        stored := "01.06-30.09"
        raw := .parsed (.dateRange (.yearlessMonthDay
          { month := 6, day := 1 } { month := 9, day := 30 }))
      }] = some "VALUE|01.06-30.09" := by
  native_decide

private def storedRange : StoredDateRange := {
  text := "2024-03-20/2024-03-21"
  nonempty := by decide
}

/- DateRange specializes the existing exact value/clear transition without entering scalar temporal indexing. -/
example :
    (DateRangeTargetOutcome.accepted storedRange).applyTo .presentEmpty =
        .presentValue storedRange ∧
      DateRangeTargetOutcome.noValue.applyTo .absent = .absent ∧
      DateRangeTargetOutcome.noValue.applyTo (.presentValue storedRange) =
        .presentEmpty := by
  decide

end A12Kernel.Conformance.DateRangeFirstFilledComputation
