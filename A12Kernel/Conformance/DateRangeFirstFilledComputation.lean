import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Semantics.TemporalApplication

/-! # Bounded DateRange `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.DateRangeFirstFilledComputation

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd")
    (separator : String := "/") : FlatFieldDecl := {
  id
  groupPath
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
  repeatableScope := scope
}

private def target := rangeField 1 ["Cart"] "FirstWindow"
private def source := rangeField 2 ["Cart", "Lines"] "Window" [10]
private def otherFormatSource :=
  rangeField 3 ["Cart", "Lines"] "DottedWindow" [10] "dd.MM.yyyy" "-"
private def otherSeparatorTarget :=
  rangeField 4 ["Cart"] "DashedWindow" [] "yyyy-MM-dd" "-"
private def otherSeparatorSource :=
  rangeField 5 ["Cart", "Lines"] "DashedSource" [10] "yyyy-MM-dd" "-"
private def dottedTarget :=
  rangeField 6 ["Cart"] "DottedTarget" [] "dd.MM.yyyy" "-"
private def dottedSource :=
  rangeField 7 ["Cart", "Lines"] "DottedSource" [10] "dd.MM.yyyy" "-"
private def unsupportedDottedTarget :=
  rangeField 8 ["Cart"] "UnsupportedDottedTarget" [] "dd.MM.yyyy" "/"
private def unsupportedDottedSource :=
  rangeField 9 ["Cart", "Lines"] "UnsupportedDottedSource" [10]
    "dd.MM.yyyy" "/"
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
private def directDottedFirst :=
  rangeField 18 ["Cart"] "DirectDottedFirst" [] "dd.MM.yyyy" "-"
private def directDottedSecond :=
  rangeField 19 ["Cart"] "DirectDottedSecond" [] "dd.MM.yyyy" "-"
private def directIsoSource :=
  rangeField 20 ["Cart"] "DirectIsoSource" [] "yyyy-MM-dd" "/"
private def directDottedThird :=
  rangeField 21 ["Cart"] "DirectDottedThird" [] "dd.MM.yyyy" "-"

private def model : FlatModel := {
  fields := [target, source, otherFormatSource, otherSeparatorTarget,
    otherSeparatorSource, dottedTarget, dottedSource, unsupportedDottedTarget,
    unsupportedDottedSource, yearTarget, yearSource, yearMonthTarget,
    yearMonthSource, monthTarget, monthSource, monthDayTarget, monthDaySource,
    directDottedFirst, directDottedSecond, directIsoSource, directDottedThird]
  repeatableGroups := [
    { level := 10, path := ["Cart", "Lines"], repeatability := some 99 }]
  timeZoneId := "UTC"
}

private def configuredModel : FlatModel := { model with baseYear := some 2024 }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Cart" }, { name := "Lines", starred := true }]
  field
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def directSource (first second : String) : SurfaceFieldEntitySource := {
  first := .field (bare first)
  rest := [.field (bare second)]
}

private def directSourceList (first : String) (rest : List String) :
    SurfaceFieldEntitySource := {
  first := .field (bare first)
  rest := rest.map fun field => .field (bare field)
}

private def projectedThirdSource : SurfaceFieldEntitySource := {
  first := .field (bare "DirectDottedFirst")
  rest := [.field (bare "DirectDottedSecond"),
    .field (bare "DirectDottedThird") (.projected "Category")]
}

private def checkedFor? (candidate : FlatModel)
    (targetField : FieldId) (field : String) :=
  (checkDateRangeFirstFilledComputation
    candidate ["Cart"] targetField (star field)).toOption

private def checked? := checkedFor? model

private def directChecked? (targetField : FieldId) (first second : String) :=
  (checkDateRangeFirstFilledDirectComputation model ["Cart"] targetField
    (directSource first second)).toOption

private def directDiagnostic? (targetField : FieldId) (first second : String) :=
  match checkDateRangeFirstFilledDirectComputation model ["Cart"] targetField
      (directSource first second) with
  | .ok _ => none
  | .error cause => cause.diagnostic?

private def directListChecked? (targetField : FieldId) (first : String)
    (rest : List String) :=
  (checkDateRangeFirstFilledDirectComputation model ["Cart"] targetField
    (directSourceList first rest)).toOption

private def directListDiagnostic? (targetField : FieldId) (first : String)
    (rest : List String) :=
  match checkDateRangeFirstFilledDirectComputation model ["Cart"] targetField
      (directSourceList first rest) with
  | .ok _ => none
  | .error cause => cause.diagnostic?

private def directListSourceIds? (targetField : FieldId) (first : String)
    (rest : List String) : Option (List FieldId) := do
  let operation ← directListChecked? targetField first rest
  pure (operation.sources.map fun source => source.direct.source.id)

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

private structure DirectInput where
  declaration : FlatFieldDecl
  stored : String
  raw : RawCell

private def directInputFor? (inputs : List DirectInput) :
    Option (CheckedDocument model) := do
  let prepared ← preparedFor? model
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := inputs.map fun input => {
      address := { field := input.declaration.id, path := [] }
      stored := input.stored
      raw := input.raw
    }
  }).toOption

private def directSignature? (inputs : List DirectInput) : Option String := do
  let operation ← directChecked? dottedTarget.id
    "DirectDottedFirst" "DirectDottedSecond"
  let input ← directInputFor? inputs
  let outcome ← (operation.execute input).toOption
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .errored stored _ => "ERRORED|" ++ stored.text
    | .poison _ => "POISON")

private def directTripleSignature? (inputs : List DirectInput) : Option String := do
  let operation ← directListChecked? dottedTarget.id "DirectDottedFirst"
    ["DirectDottedSecond", "DirectDottedThird"]
  let input ← directInputFor? inputs
  let outcome ← (operation.execute input).toOption
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .errored stored _ => "ERRORED|" ++ stored.text
    | .poison _ => "POISON")

/- The retained temporal-family probe Kernel-calibrates these exact all-empty and first-row-filled result signatures. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [{
        row := 1
        stored := "2024-03-20/2024-03-21"
        raw := .parsed (.dateRange selectedRange)
      }] = some "VALUE|2024-03-20/2024-03-21" := by
  native_decide

/- The finite direct list admits a third matching source while retaining profile and target-self-reference diagnostics at that later position. -/
example :
    (directListChecked? dottedTarget.id "DirectDottedFirst"
      ["DirectDottedSecond", "DirectDottedThird"]).isSome = true ∧
      directListSourceIds? dottedTarget.id "DirectDottedFirst"
        ["DirectDottedSecond", "DirectDottedThird"] = some [18, 19, 21] ∧
      directListDiagnostic? dottedTarget.id "DirectDottedFirst"
        ["DirectDottedSecond", "DirectIsoSource"] =
          some .varyingTypesNotAllowed ∧
      directListDiagnostic? dottedTarget.id "DirectDottedFirst"
        ["DirectDottedSecond", "DottedTarget"] =
          some .errorReferenceToCalculatedField ∧
      directListDiagnostic? dottedTarget.id "DirectDottedFirst" [] =
        some .paramSizeInvalidN ∧
      (checkDateRangeFirstFilledDirectComputation model ["Cart"]
        dottedTarget.id projectedThirdSource).toOption.isNone = true := by
  native_decide

/- Three direct fields preserve authored-order recursion: two empty prefixes reach the third value, while a second-position value or formal cause hides the third selection result. -/
example :
    directTripleSignature? [{
      declaration := directDottedFirst, stored := "", raw := .presentEmpty
    }, {
      declaration := directDottedSecond, stored := "", raw := .presentEmpty
    }, {
      declaration := directDottedThird
      stored := "01.07.2024-31.07.2024"
      raw := .parsed (.dateRange (exactRange
        1719792000000 1722384000000 2024 7 1 2024 7 31))
    }] = some "VALUE|01.07.2024-31.07.2024" ∧
      directTripleSignature? [{
        declaration := directDottedFirst, stored := "", raw := .presentEmpty
      }, {
        declaration := directDottedSecond
        stored := "01.06.2024-30.06.2024"
        raw := .parsed (.dateRange (exactRange
          1717200000000 1719705600000 2024 6 1 2024 6 30))
      }, {
        declaration := directDottedThird
        stored := "garbage"
        raw := .rejected .dateRangeSeparator
      }] = some "VALUE|01.06.2024-30.06.2024" ∧
      directTripleSignature? [{
        declaration := directDottedFirst, stored := "", raw := .presentEmpty
      }, {
        declaration := directDottedSecond
        stored := "garbage"
        raw := .rejected .dateRangeSeparator
      }, {
        declaration := directDottedThird
        stored := "01.07.2024-31.07.2024"
        raw := .parsed (.dateRange (exactRange
          1719792000000 1722384000000 2024 7 1 2024 7 31))
      }] = some "POISON" := by
  native_decide

/- The exact direct-field-list shape admits only one shared declaration profile and retains the shared entity-list cardinality/duplicate gates. -/
example :
    (directChecked? dottedTarget.id
      "DirectDottedFirst" "DirectDottedSecond").isSome = true ∧
      directDiagnostic? dottedTarget.id
        "DirectDottedFirst" "DirectIsoSource" =
          some .varyingTypesNotAllowed ∧
      directDiagnostic? dottedTarget.id
        "DottedTarget" "DirectDottedSecond" =
          some .errorReferenceToCalculatedField ∧
      directDiagnostic? dottedTarget.id
        "DirectDottedFirst" "DottedTarget" =
          some .errorReferenceToCalculatedField ∧
      (directChecked? dottedTarget.id
        "DirectDottedFirst" "DirectDottedFirst").isNone = true := by
  native_decide

/- Direct fields are scanned in authored order: empty continues, a present value hides a later formal cell, and a reached formal cell hides a later value. -/
example :
    directSignature? [] = some "CLEARED" ∧
      directSignature? [{
      declaration := directDottedFirst
      stored := ""
      raw := .presentEmpty
    }, {
      declaration := directDottedSecond
      stored := "01.06.2024-30.06.2024"
      raw := .parsed (.dateRange (exactRange
        1717200000000 1719705600000 2024 6 1 2024 6 30))
    }] = some "VALUE|01.06.2024-30.06.2024" ∧
      directSignature? [{
        declaration := directDottedFirst
        stored := "01.05.2024-31.05.2024"
        raw := .parsed (.dateRange (exactRange
          1714521600000 1717113600000 2024 5 1 2024 5 31))
      }, {
        declaration := directDottedSecond
        stored := "garbage"
        raw := .rejected .dateRangeSeparator
      }] = some "VALUE|01.05.2024-31.05.2024" ∧
      directSignature? [{
        declaration := directDottedFirst
        stored := "garbage"
        raw := .rejected .dateRangeSeparator
      }, {
        declaration := directDottedSecond
        stored := "01.06.2024-30.06.2024"
        raw := .parsed (.dateRange (exactRange
          1717200000000 1719705600000 2024 6 1 2024 6 30))
      }] = some "POISON" := by
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

/- The second exact legal declaration pair selects and renders the same checked typed endpoint payload. Static admission and the renderer are externally established separately; their direct `FirstFilledValue` composition remains external-evidence pending. -/
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

/- Both declarations must share one exact admitted DateRange pair; crossing the two legal pairs or changing only the ISO separator remains refused. -/
example :
    (checked? target.id "Window").isSome = true ∧
      (checked? target.id "DottedWindow").isNone = true ∧
      (checked? dottedTarget.id "Window").isNone = true ∧
      (checked? dottedTarget.id "DottedSource").isSome = true ∧
      (checked? target.id "DashedSource").isNone = true ∧
      (checked? otherSeparatorTarget.id "Window").isNone = true ∧
      (checked? unsupportedDottedTarget.id "UnsupportedDottedSource").isNone =
        true := by
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
