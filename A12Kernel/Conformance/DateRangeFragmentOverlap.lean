import A12Kernel.Elaboration.DateRangeOverlap

/-! # Direct DateFragment range overlap locks

These cases isolate the measured singular direct fragment profiles from the canonical and plural overlap matrix. `yyyy-MM` is year-bearing by itself; `MM` and `MM-dd` become exact only through the model's Base Year. Starred and plural fragment routes remain outside this boundary.
-/

namespace A12Kernel.Conformance.DateRangeFragmentOverlap

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd") :
    FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator := "/" }
}

private def model : FlatModel := {
  fields := [
    rangeField 1 ["Form"] "Probe",
    rangeField 2 ["Form"] "YearMonth" [] "yyyy-MM",
    rangeField 3 ["Form"] "Year" [] "yyyy",
    rangeField 4 ["Form", "Rows"] "FragmentWindow" [10] "yyyy-MM",
    rangeField 5 ["Form"] "Month" [] "MM",
    rangeField 6 ["Form"] "MonthDay" [] "MM-dd"]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3 }]
}

private def model2024 : FlatModel := { model with baseYear := some 2024 }
private def model2023 : FlatModel := { model with baseYear := some 2023 }

private def direct (field : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field }

private def fragmentStar : SurfaceFieldEntityOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "FragmentWindow"
  }

private def checkedSource? (checkedModel : FlatModel)
    (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Option (CheckedDateRangesOverlapSource checkedModel) :=
  (elaborateDateRangesOverlapSource checkedModel ["Form"] { first, rest }).toOption

private def admissionError? (checkedModel : FlatModel)
    (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Option DateRangesOverlapElabError :=
  match elaborateDateRangesOverlapSource checkedModel ["Form"] { first, rest } with
  | .ok _ => none
  | .error error => some error

private def pluralAdmissionError? (checkedModel : FlatModel)
    (scalar first : SurfaceFieldEntityOperand) :
    Option AtLeastOneDateRangeOverlapsElabError :=
  match elaborateAtLeastOneDateRangeOverlapsSource checkedModel ["Form"] {
      scalar
      list := { first, rest := [] }
    } with
  | .ok _ => none
  | .error error => some error

/- Year-month direct admission stays singular, exact-profile, and non-starred. -/
example :
    (checkedSource? model (direct "YearMonth") [direct "Probe"]).isSome = true ∧
      admissionError? model fragmentStar [direct "Probe"] =
        some (.unsupportedPolicy ["Form", "Rows", "FragmentWindow"]
          "yyyy-MM" "/") ∧
      admissionError? model (direct "Year") [direct "Probe"] =
        some (.unsupportedPolicy ["Form", "Year"] "yyyy" "/") ∧
      pluralAdmissionError? model (direct "Probe") (direct "YearMonth") =
        some (.unsupportedPolicy .list ["Form", "YearMonth"] "yyyy-MM" "/") := by
  native_decide

/- Base Year admits both shorter profiles only on the singular direct route. -/
example :
    (checkedSource? model2024 (direct "Month") [direct "Probe"]).isSome = true ∧
      (checkedSource? model2024 (direct "Probe") [direct "MonthDay"]).isSome =
        true ∧
      pluralAdmissionError? model2024 (direct "Probe") (direct "Month") =
        some (.unsupportedPolicy .list ["Form", "Month"] "MM" "/") := by
  native_decide

/- Without Base Year, only a full-year pair gets the measured diagnostic; an all-yearless pair stays unmapped. -/
example :
    (admissionError? model (direct "Month") [direct "Probe"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "Probe") [direct "Month"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "MonthDay") [direct "Probe"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "Probe") [direct "MonthDay"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      admissionError? model (direct "Month") [direct "MonthDay"] =
        some (.unsupportedPolicy ["Form", "Month"] "MM" "/") := by
  native_decide

/- The new diagnostic keeps its exact observable Kernel identity. -/
example : KernelStaticDiagnostic.dateWithAndWithoutYear.kernelCode =
    "MVK_DATE_WITH_AND_WITHOUT_YEAR" := by
  native_decide

private def dateValue (year : Int) (epochMillis : Int)
    (month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def rangeValue (year : Int) (startMillis finishMillis : Int)
    (startMonth startDay finishMonth finishDay : Nat) : DateRangeValue := {
  start := dateValue year startMillis startMonth startDay
  finish := dateValue year finishMillis finishMonth finishDay
}

private def rangeCell (field : FieldId) (stored : String)
    (value : DateRangeValue) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw := .parsed (.dateRange (.exact value))
}

private def verdict? (checkedModel : FlatModel)
    (first : SurfaceFieldEntityOperand) (rest : List SurfaceFieldEntityOperand)
    (cells : List ClassifiedCellInput) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler checkedModel).toOption
  let source ← checkedSource? checkedModel first rest
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption
  (source.evaluateCheckedDocument document []).toOption.map (·.verdict)

private def february2024 :=
  rangeValue 2024 1706745600000 1709164800000 2 1 2 29
private def februaryFirst2024 :=
  rangeValue 2024 1706745600000 1706745600000 2 1 2 1
private def februaryLast2024 :=
  rangeValue 2024 1709164800000 1709164800000 2 29 2 29
private def marchFirst2024 :=
  rangeValue 2024 1709251200000 1709251200000 3 1 3 1
private def februaryLast2023 :=
  rangeValue 2023 1677542400000 1677542400000 2 28 2 28
private def marchFirst2023 :=
  rangeValue 2023 1677628800000 1677628800000 3 1 3 1
private def february2023 :=
  rangeValue 2023 1675209600000 1677542400000 2 1 2 28

/- The year-bearing fragment reaches leap day but not the next day. -/
example :
    verdict? model (direct "YearMonth") [direct "Probe"] [
      rangeCell 2 "2024-02/2024-02" february2024,
      rangeCell 1 "2024-02-29/2024-02-29" februaryLast2024] =
        some (.fired .value) ∧
      verdict? model (direct "Probe") [direct "YearMonth"] [
        rangeCell 1 "2024-03-01/2024-03-01" marchFirst2024,
        rangeCell 2 "2024-02/2024-02" february2024] = some .notFired := by
  native_decide

/- Configured `MM` spans the whole leap or ordinary month; `MM-dd` remains one exact day. -/
example :
    verdict? model2024 (direct "Month") [direct "Probe"] [
      rangeCell 5 "02/02" february2024,
      rangeCell 1 "2024-02-01/2024-02-01" februaryFirst2024] =
        some (.fired .value) ∧
      verdict? model2024 (direct "Month") [direct "Probe"] [
        rangeCell 5 "02/02" february2024,
        rangeCell 1 "2024-02-29/2024-02-29" februaryLast2024] =
          some (.fired .value) ∧
      verdict? model2024 (direct "Probe") [direct "Month"] [
        rangeCell 1 "2024-03-01/2024-03-01" marchFirst2024,
        rangeCell 5 "02/02" february2024] = some .notFired ∧
      verdict? model2024 (direct "MonthDay") [direct "Probe"] [
        rangeCell 6 "02-29/02-29" februaryLast2024,
        rangeCell 1 "2024-02-29/2024-02-29" februaryLast2024] =
          some (.fired .value) := by
  native_decide

/- Nonleap Base Year moves both the month end and exact month-day boundary to February 28. -/
example :
    verdict? model2023 (direct "Month") [direct "Probe"] [
      rangeCell 5 "02/02" february2023,
      rangeCell 1 "2023-02-28/2023-02-28" februaryLast2023] =
        some (.fired .value) ∧
      verdict? model2023 (direct "Probe") [direct "Month"] [
        rangeCell 1 "2023-03-01/2023-03-01" marchFirst2023,
        rangeCell 5 "02/02" february2023] = some .notFired ∧
      verdict? model2023 (direct "MonthDay") [direct "Probe"] [
        rangeCell 6 "02-28/02-28" februaryLast2023,
        rangeCell 1 "2023-02-28/2023-02-28" februaryLast2023] =
          some (.fired .value) := by
  native_decide

end A12Kernel.Conformance.DateRangeFragmentOverlap
