import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Elaboration.TemporalErroredComputationApplication

/-! # Direct-list DateRange FirstFilledValue computation locks -/

namespace A12Kernel.Conformance.DateRangeFirstFilledDirectComputation

open A12Kernel

private def rangeField (id : FieldId) (name : String)
    (format : String := "yyyy-MM-dd") (separator : String := "/")
    (interpretationOfYear : Option DateRangeYearInterpretation := none) :
    FlatFieldDecl := {
  id
  groupPath := ["Cart"]
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator, interpretationOfYear }
  repeatableScope := []
}

private def target := rangeField 1 "FirstWindow"
private def dottedTarget := rangeField 6 "DottedTarget" "dd.MM.yyyy" "-"
private def yearTarget := rangeField 10 "YearTarget" "yyyy" "/"
private def yearMonthTarget := rangeField 12 "YearMonthTarget" "yyyy-MM" "/"
private def monthTarget := rangeField 14 "MonthTarget" "MM" "/"
private def monthDayTarget := rangeField 16 "MonthDayTarget" "MM-dd" "/"

private def directDottedFirst :=
  rangeField 18 "DirectDottedFirst" "dd.MM.yyyy" "-"
private def directDottedSecond :=
  rangeField 19 "DirectDottedSecond" "dd.MM.yyyy" "-"
private def directIsoSource :=
  rangeField 20 "DirectIsoSource" "yyyy-MM-dd" "/"
private def directDottedThird :=
  rangeField 21 "DirectDottedThird" "dd.MM.yyyy" "-"
private def directYearFirst := rangeField 22 "DirectYearFirst" "yyyy" "/"
private def directYearSecond := rangeField 23 "DirectYearSecond" "yyyy" "/"
private def directYearThird := rangeField 24 "DirectYearThird" "yyyy" "/"
private def directYearMonthFirst := rangeField 25 "DirectYearMonthFirst" "yyyy-MM" "/"
private def directYearMonthSecond := rangeField 26 "DirectYearMonthSecond" "yyyy-MM" "/"
private def directYearMonthThird := rangeField 27 "DirectYearMonthThird" "yyyy-MM" "/"
private def directMonthFirst := rangeField 28 "DirectMonthFirst" "MM" "/"
private def directMonthSecond := rangeField 29 "DirectMonthSecond" "MM" "/"
private def directMonthThird := rangeField 30 "DirectMonthThird" "MM" "/"
private def directMonthDayFirst := rangeField 31 "DirectMonthDayFirst" "MM-dd" "/"
private def directMonthDaySecond := rangeField 32 "DirectMonthDaySecond" "MM-dd" "/"
private def directMonthDayThird := rangeField 33 "DirectMonthDayThird" "MM-dd" "/"
private def directMonthEmptyFirst :=
  rangeField 34 "DirectMonthEmptyFirst" "MM" ""
private def directMonthEmptySecond :=
  rangeField 35 "DirectMonthEmptySecond" "MM" ""

private def directFromFirst :=
  rangeField 36 "DirectFromFirst" "dd.MM" "-" (some .anchorStart)
private def directFromSecond :=
  rangeField 37 "DirectFromSecond" "dd.MM" "-" (some .anchorStart)
private def directToTarget :=
  rangeField 38 "DirectToTarget" "dd.MM" "-" (some .anchorFinish)
private def directToFirst :=
  rangeField 39 "DirectToFirst" "dd.MM" "-" (some .anchorFinish)
private def directFromTarget :=
  rangeField 41 "DirectFromTarget" "dd.MM" "-" (some .anchorStart)

/-- A fixed DateRange target outside the declaring group, whose sources stay inside it. Its profile
matches the dotted list so the placement cell below is not decided by the comparability gate. -/
private def otherGroupTarget : FlatFieldDecl :=
  { rangeField 42 "OtherWindow" "dd.MM.yyyy" "-" with groupPath := ["Other"] }

/-- A source outside the declaring group. A bare operand name resolves against that group, so this
one is unreachable from the admitted spelling — the refusal below is resolution, not the capsule's
own source-group narrowing, and either way it carries no Kernel code. -/
private def otherGroupSource : FlatFieldDecl :=
  { rangeField 43 "OtherSource" "dd.MM.yyyy" "-" with groupPath := ["Other"] }

private def model : FlatModel := {
  fields := [target, dottedTarget, yearTarget, yearMonthTarget, monthTarget,
    monthDayTarget, directDottedFirst, directDottedSecond, directIsoSource,
    directDottedThird, directYearFirst, directYearSecond, directYearThird,
    directYearMonthFirst, directYearMonthSecond, directYearMonthThird,
    directMonthFirst, directMonthSecond, directMonthThird, directMonthDayFirst,
    directMonthDaySecond, directMonthDayThird, directMonthEmptyFirst,
    directMonthEmptySecond, directFromFirst, directFromSecond, directToTarget,
    directToFirst, directFromTarget, otherGroupTarget, otherGroupSource]
  repeatableGroups := []
  timeZoneId := "UTC"
}

private def interpretationModel : FlatModel := { model with baseYear := some 2020 }

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

private def directChecked? (targetField : FieldId) (first second : String) :=
  (checkDateRangeFirstFilledDirectComputation model ["Cart"] targetField
    (directSource first second)).toOption

private def directDiagnostic? (targetField : FieldId) (first second : String) :=
  match checkDateRangeFirstFilledDirectComputation model ["Cart"] targetField
      (directSource first second) with
  | .ok _ => none
  | .error cause => cause.diagnostic?

private def directListCheckedFor? (candidate : FlatModel) (targetField : FieldId)
    (first : String) (rest : List String) :=
  (checkDateRangeFirstFilledDirectComputation candidate ["Cart"] targetField
    (directSourceList first rest)).toOption

private def directListChecked? := directListCheckedFor? model

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

private def directInputForModel? (candidate : FlatModel) (inputs : List DirectInput) :
    Option (CheckedDocument candidate) := do
  let prepared ← preparedFor? candidate
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := inputs.map fun input => {
      address := { field := input.declaration.id, path := [] }
      stored := input.stored
      raw := input.raw
    }
  }).toOption

private def directInputFor? := directInputForModel? model

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

private def directListSignatureForModel? (candidate : FlatModel)
    (targetField : FieldId) (first : String) (rest : List String)
    (inputs : List DirectInput) : Option String := do
  let operation ← directListCheckedFor? candidate targetField first rest
  let input ← directInputForModel? candidate inputs
  let outcome ← (operation.execute input).toOption
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .errored stored _ => "ERRORED|" ++ stored.text
    | .poison _ => "POISON")

private def directListSignature? := directListSignatureForModel? model

private def selectedRange : DateRangeCellValue := exactRange
  1717200000000 1719705600000 2024 6 1 2024 6 30
private def seedRange : DateRangeCellValue := exactRange
  1710028800000 1710115200000 2024 3 10 2024 3 11

private def selectedStored : StoredDateRange :=
  ⟨"2024-06-01/2024-06-30", by decide⟩
private def seedStored : StoredDateRange :=
  ⟨"2024-03-10/2024-03-11", by decide⟩
private def unrelatedStored : StoredDateRange :=
  ⟨"10.03.2024-11.03.2024", by decide⟩

private def directRunView? (targetStored : String) (targetRaw : RawCell)
    (sourceInputs : List DirectInput)
    (residualMessages : List FormalCause := []) :
    Option (DateRangeComputationRunView FormalCause) := do
  let operation ← directListChecked? target.id "DirectDottedFirst"
    ["DirectDottedSecond"]
  let input ← directInputFor? ({
    declaration := target
    stored := targetStored
    raw := targetRaw
  } :: sourceInputs)
  operation.executeResult input residualMessages |>.toOption

private def destinationFor? (includeTarget : Bool) :
    Option (CheckedDocument model) :=
  let targetInputs := if includeTarget then [{
    declaration := target
    stored := seedStored.text
    raw := .parsed (.dateRange seedRange)
  }] else []
  directInputFor? (targetInputs ++ [{
    declaration := dottedTarget
    stored := unrelatedStored.text
    raw := .parsed (.dateRange seedRange)
  }])

/- The checked direct-list operation classifies its target-rendered lexical crossing and applies only the retained change to a separate checked destination while preserving unrelated state. -/
example : (do
    let view ← directRunView? seedStored.text
      (.parsed (.dateRange seedRange)) [{
        declaration := directDottedFirst
        stored := "01.06.2024-30.06.2024"
        raw := .parsed (.dateRange selectedRange)
      }]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges,
      applied target.id, applied dottedTarget.id)) =
    some ([{ targetField := target.id, value := selectedStored }],
      [{ targetField := target.id, value := selectedStored }],
      .presentValue selectedStored, .presentValue unrelatedStored) := by
  native_decide

/- Change classification remains source-relative after direct-list target rendering: an equal source target is public but inert against a different destination target. -/
example : (do
    let view ← directRunView? selectedStored.text
      (.parsed (.dateRange selectedRange)) [{
        declaration := directDottedFirst
        stored := "01.06.2024-30.06.2024"
        raw := .parsed (.dateRange selectedRange)
      }]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges, applied target.id)) =
    some ([{ targetField := target.id, value := selectedStored }], [],
      .presentValue seedStored) := by
  native_decide

/- List exhaustion and a reached formal cause both retain a source-filled clear and materialize an absent destination target without disturbing unrelated state. -/
example :
    (do
      let view ← directRunView? seedStored.text
        (.parsed (.dateRange seedRange)) []
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied dottedTarget.id)) =
      some ([target.id], true, .presentEmpty,
        .presentValue unrelatedStored) ∧
    (do
      let view ← directRunView? seedStored.text
        (.parsed (.dateRange seedRange)) [{
          declaration := directDottedFirst
          stored := "garbage"
          raw := .rejected .dateRangeSeparator
        }]
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied dottedTarget.id)) =
      some ([target.id], true, .presentEmpty,
        .presentValue unrelatedStored) := by
  native_decide

/- Every fragment policy admits the same three-direct-field shape, while a later crossed fragment retains the exact list-family diagnostic. -/
example :
    (directListChecked? yearTarget.id "DirectYearFirst"
      ["DirectYearSecond", "DirectYearThird"]).isSome = true ∧
      (directListChecked? yearMonthTarget.id "DirectYearMonthFirst"
        ["DirectYearMonthSecond", "DirectYearMonthThird"]).isSome = true ∧
      (directListChecked? monthTarget.id "DirectMonthFirst"
        ["DirectMonthSecond", "DirectMonthThird"]).isSome = true ∧
      (directListChecked? monthDayTarget.id "DirectMonthDayFirst"
        ["DirectMonthDaySecond", "DirectMonthDayThird"]).isSome = true ∧
      directListDiagnostic? yearTarget.id "DirectYearFirst"
        ["DirectYearSecond", "DirectYearMonthThird"] =
          some .varyingTypesNotAllowed := by
  native_decide

/- Fragment lists reuse the recursive scan and declaration-owned target rendering, including yearless component identity without Base Year. -/
example :
    directListSignature? yearTarget.id "DirectYearFirst"
      ["DirectYearSecond", "DirectYearThird"] [] = some "CLEARED" ∧
      directListSignature? yearTarget.id "DirectYearFirst"
        ["DirectYearSecond", "DirectYearThird"] [{
          declaration := directYearThird
          stored := "2024/2025"
          raw := .parsed (.dateRange (exactRange
            1704067200000 1767139200000 2024 1 1 2025 12 31))
        }] = some "VALUE|2024/2025" ∧
      directListSignature? yearMonthTarget.id "DirectYearMonthFirst"
        ["DirectYearMonthSecond", "DirectYearMonthThird"] [{
          declaration := directYearMonthThird
          stored := "2024-12/2025-02"
          raw := .parsed (.dateRange (exactRange
            1733011200000 1740700800000 2024 12 1 2025 2 28))
        }] = some "VALUE|2024-12/2025-02" ∧
      directListSignature? monthTarget.id "DirectMonthFirst"
        ["DirectMonthSecond", "DirectMonthThird"] [{
          declaration := directMonthThird
          stored := "01/02"
          raw := .parsed (.dateRange (.yearlessMonth 1 2))
        }] = some "VALUE|01/02" ∧
      directListSignature? monthDayTarget.id "DirectMonthDayFirst"
        ["DirectMonthDaySecond", "DirectMonthDayThird"] [{
          declaration := directMonthDayThird
          stored := "01-31/02-29"
          raw := .parsed (.dateRange (.yearlessMonthDay
            { month := 1, day := 31 } { month := 2, day := 29 }))
        }] = some "VALUE|01-31/02-29" := by
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

/- Placement is unconstrained. The target sits in `["Other"]` while the declaring group and every source stay in `["Cart"]`, and the list is still admitted: nothing in a direct nonrepeatable list iterates, so the Kernel's containment gate cannot fire. Measured at the [fixed-target star placement checkpoint](../../docs/SOURCES.md#src-fixed-target-star-placement), whose direct-list row admits this shape at four placements. The sources must still share the declaring group; that is this capsule's own bounded subset, and a bare operand name cannot even spell a source outside it. Either refusal carries no Kernel code, so the second cell asserts exactly that and claims no diagnostic class. -/
example :
    (checkDateRangeFirstFilledDirectComputation model ["Cart"]
      otherGroupTarget.id
      (directSource "DirectDottedFirst" "DirectDottedSecond")).toOption.isSome
      = true ∧
    directDiagnostic? otherGroupTarget.id "DirectDottedFirst" "OtherSource" = none := by
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

/- A declared year interpretation changes neither direct-list admission nor target rendering. The source is read through its own resolved endpoint years, while the target stores the component spelling selected by its own declaration. The two directions therefore preserve identical wrapping text even though FROM and TO resolve it to different exact ranges; exhaustion keeps the ordinary clear result. -/
example :
    (directListCheckedFor? interpretationModel directToTarget.id "DirectFromFirst"
      ["DirectFromSecond"]).isSome = true ∧
      (directListCheckedFor? interpretationModel directFromTarget.id "DirectToFirst"
        ["DirectFromSecond"]).isSome = true := by
  native_decide

example :
    directListSignatureForModel? interpretationModel directToTarget.id "DirectFromFirst"
      ["DirectFromSecond"] [{
        declaration := directFromFirst
        stored := "01.11-28.02"
        raw := .parsed (.dateRange (exactRange
          1604188800000 1614470400000 2020 11 1 2021 2 28))
    }] = some "VALUE|01.11-28.02" ∧
    directListSignatureForModel? interpretationModel directFromTarget.id "DirectToFirst"
      ["DirectFromSecond"] [{
        declaration := directToFirst
        stored := "01.11-28.02"
        raw := .parsed (.dateRange (exactRange
          1572566400000 1582848000000 2019 11 1 2020 2 28))
      }] = some "VALUE|01.11-28.02" := by
  native_decide

example :
    directListSignatureForModel? interpretationModel directToTarget.id "DirectFromFirst"
      ["DirectFromSecond"] [] = some "CLEARED" ∧
    directListSignatureForModel? interpretationModel directFromTarget.id "DirectToFirst"
      ["DirectFromSecond"] [] = some "CLEARED" := by
  native_decide

/- The direct-list route applies two ordered gates the Kernel keeps distinct. Every source must
repeat the **identical** declared format, so a same-component crossing inside the list is
refused `MVK_VARYING_TYPES_NOT_ALLOWED` even where the component sets agree; that gate decides
first, before the target is consulted. The shared source format then only has to expose the
**target's** component set, so a list of dotted sources feeds an ISO target and a list of
empty-separator month sources feeds a slash-separated month target. A genuinely different
component set is refused `MVK_INVALID_COMPARE_TO_DATE_RANGE`. -/
example :
    (directChecked? target.id "DirectDottedFirst" "DirectDottedSecond").isSome =
        true ∧
      (directChecked? monthTarget.id "DirectMonthEmptyFirst"
        "DirectMonthEmptySecond").isSome = true ∧
      directDiagnostic? target.id "DirectDottedFirst" "DirectIsoSource" =
        some .varyingTypesNotAllowed ∧
      directListDiagnostic? target.id "DirectDottedFirst"
          ["DirectDottedSecond", "DirectIsoSource"] =
        some .varyingTypesNotAllowed ∧
      directDiagnostic? target.id "DirectMonthEmptyFirst"
        "DirectMonthEmptySecond" = some .invalidCompareToDateRange ∧
      directDiagnostic? monthTarget.id "DirectDottedFirst"
        "DirectDottedSecond" = some .invalidCompareToDateRange := by
  native_decide

/- On an admitted crossing the target's own spelling renders the selected value, so a dotted
source list stores ISO text on an ISO target. The source profile decides nothing about the
output, which is the whole observable consequence of admitting the cross. -/
example :
    directListSignature? target.id "DirectDottedFirst" ["DirectDottedSecond"]
        [{ declaration := directDottedFirst
           stored := "01.06.2024-30.06.2024"
           raw := .parsed (.dateRange (exactRange 1717200000000 1719705600000
             2024 6 1 2024 6 30)) }] =
      some "VALUE|2024-06-01/2024-06-30" ∧
    directListSignature? monthTarget.id "DirectMonthEmptyFirst"
        ["DirectMonthEmptySecond"]
        [{ declaration := directMonthEmptyFirst
           stored := "0609"
           raw := .parsed (.dateRange (.yearlessMonth 6 9)) }] =
      some "VALUE|06/09" ∧
    directListSignature? target.id "DirectDottedFirst" ["DirectDottedSecond"]
        [{ declaration := directDottedSecond
           stored := "02.07.2024-31.07.2024"
           raw := .parsed (.dateRange (exactRange 1719878400000 1722384000000
             2024 7 2 2024 7 31)) }] =
      some "VALUE|2024-07-02/2024-07-31" := by
  native_decide

end A12Kernel.Conformance.DateRangeFirstFilledDirectComputation
