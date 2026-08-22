import A12Kernel.Elaboration.AtLeastOneDateRangeOverlap

/-! # Direct DateFragment range overlap locks

These cases isolate the singular direct fragment profiles from the canonical and plural overlap matrix. `yyyy` and `yyyy-MM` are year-bearing by themselves; `MM` and `MM-dd` become exact only through the model's Base Year. Starred and plural fragment routes remain outside this boundary. Direct `yyyy` overlap remains external evidence pending.
-/

namespace A12Kernel.Conformance.DateRangeFragmentOverlap

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd")
    (separator : String := "/") :
    FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def model : FlatModel := {
  fields := [
    rangeField 1 ["Form"] "Probe",
    rangeField 2 ["Form"] "YearMonth" [] "yyyy-MM",
    rangeField 3 ["Form"] "Year" [] "yyyy",
    rangeField 4 ["Form", "Rows"] "FragmentWindow" [10] "yyyy-MM",
    rangeField 5 ["Form"] "Month" [] "MM",
    rangeField 6 ["Form"] "MonthDay" [] "MM-dd",
    rangeField 7 ["Form"] "MonthEmpty" [] "MM" "",
    rangeField 8 ["Form"] "DayMonthDotted" [] "dd.MM" "-"]
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

/- Year-bearing direct fragments are admitted directly and stay non-starred. -/
example :
    (checkedSource? model (direct "Year") [direct "Probe"]).isSome = true ∧
      (checkedSource? model (direct "YearMonth") [direct "Probe"]).isSome = true ∧
      admissionError? model fragmentStar [direct "Probe"] =
        some (.unsupportedPolicy ["Form", "Rows", "FragmentWindow"]
          "yyyy-MM" "/") := by
  native_decide

/- Base Year admits both shorter profiles on the singular direct route. -/
example :
    (checkedSource? model2024 (direct "Month") [direct "Probe"]).isSome = true ∧
      (checkedSource? model2024 (direct "Probe") [direct "MonthDay"]).isSome =
        true := by
  native_decide

/- Without Base Year, a canonical range beside a yearless one gets the measured diagnostic in
either order; an all-yearless pair belongs to the unconfigured route and stays unmapped here. -/
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

/- The uniform-year gate is a property of the whole operand list, so it reaches both lexical
spellings of a yearless set, a list longer than a pair, and a year-bearing fragment beside a
yearless one. Every row is a measured Kernel refusal. -/
example :
    (admissionError? model (direct "MonthEmpty") [direct "Probe"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "Probe") [direct "DayMonthDotted"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "Probe")
          [direct "Month", direct "MonthDay"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "Year") [direct "Month"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      (admissionError? model (direct "YearMonth") [direct "MonthDay"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear := by
  native_decide

/- A uniformly year-bearing list is admitted whatever its component sets differ by, and a Base
Year makes every declaration year-bearing, so no configured model reaches the gate at all. -/
example :
    (checkedSource? model (direct "Probe") [direct "Year"]).isSome = true ∧
      (checkedSource? model (direct "Year") [direct "YearMonth"]).isSome = true ∧
      (checkedSource? model2024 (direct "Probe")
        [direct "MonthEmpty"]).isSome = true ∧
      (checkedSource? model2024 (direct "Probe")
        [direct "Month", direct "MonthDay"]).isSome = true ∧
      (checkedSource? model2024 (direct "Year")
        [direct "DayMonthDotted"]).isSome = true := by
  native_decide

/- The plural operator applies the same uniform-year gate over scalar and list, and admits a
fragment on either side once the class is uniform. Every row is measured on both Kernel
strategies; a uniformly yearless list stays with the unconfigured route and is refused here. -/
example :
    (pluralAdmissionError? model (direct "Probe") (direct "Month")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? =
      some .dateWithAndWithoutYear ∧
      (pluralAdmissionError? model (direct "Month") (direct "Probe")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? =
      some .dateWithAndWithoutYear ∧
      (pluralAdmissionError? model (direct "Probe") (direct "YearMonth")).isNone =
        true ∧
      (pluralAdmissionError? model (direct "Probe") (direct "Year")).isNone = true ∧
      (pluralAdmissionError? model (direct "YearMonth") (direct "Probe")).isNone =
        true ∧
      (pluralAdmissionError? model2024 (direct "Probe") (direct "Month")).isNone =
        true ∧
      (pluralAdmissionError? model2024 (direct "Month") (direct "Probe")).isNone =
        true ∧
      (pluralAdmissionError? model2024 (direct "Year") (direct "Month")).isNone =
        true := by
  native_decide

/- The new diagnostic keeps its exact observable Kernel identity. -/
example : KernelStaticDiagnostic.dateWithAndWithoutYear.kernelCode =
    "MVK_DATE_WITH_AND_WITHOUT_YEAR" := by
  native_decide

/-- Classify one stored token exactly as the checked-document route does, so no fixture here can
disagree with canonical classification or silently supply its own Base-Year completion. -/
private def storedCell (checkedModel : FlatModel) (field : FieldId)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw :=
    match checkedModel.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel checkedModel.timeZoneId
              checkedModel.baseYear policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
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

/- The year fragment reaches both calendar boundaries but not the next year. -/
example :
    verdict? model (direct "Year") [direct "Probe"] [
      storedCell model 3 "2024/2024",
      storedCell model 1 "2024-01-01/2024-01-01"] =
        some (.fired .value) ∧
      verdict? model (direct "Probe") [direct "Year"] [
        storedCell model 1 "2024-12-31/2024-12-31",
        storedCell model 3 "2024/2024"] = some (.fired .value) ∧
      verdict? model (direct "Year") [direct "Probe"] [
        storedCell model 3 "2024/2024",
        storedCell model 1 "2025-01-01/2025-01-01"] =
          some .notFired := by
  native_decide

/- The year-bearing fragment reaches leap day but not the next day. -/
example :
    verdict? model (direct "YearMonth") [direct "Probe"] [
      storedCell model 2 "2024-02/2024-02",
      storedCell model 1 "2024-02-29/2024-02-29"] =
        some (.fired .value) ∧
      verdict? model (direct "Probe") [direct "YearMonth"] [
        storedCell model 1 "2024-03-01/2024-03-01",
        storedCell model 2 "2024-02/2024-02"] = some .notFired := by
  native_decide

/- Configured `MM` spans the whole leap or ordinary month; `MM-dd` remains one exact day. -/
example :
    verdict? model2024 (direct "Month") [direct "Probe"] [
      storedCell model2024 5 "02/02",
      storedCell model2024 1 "2024-02-01/2024-02-01"] =
        some (.fired .value) ∧
      verdict? model2024 (direct "Month") [direct "Probe"] [
        storedCell model2024 5 "02/02",
        storedCell model2024 1 "2024-02-29/2024-02-29"] =
          some (.fired .value) ∧
      verdict? model2024 (direct "Probe") [direct "Month"] [
        storedCell model2024 1 "2024-03-01/2024-03-01",
        storedCell model2024 5 "02/02"] = some .notFired ∧
      verdict? model2024 (direct "MonthDay") [direct "Probe"] [
        storedCell model2024 6 "02-29/02-29",
        storedCell model2024 1 "2024-02-29/2024-02-29"] =
          some (.fired .value) := by
  native_decide

/- Nonleap Base Year moves both the month end and exact month-day boundary to February 28. -/
example :
    verdict? model2023 (direct "Month") [direct "Probe"] [
      storedCell model2023 5 "02/02",
      storedCell model2023 1 "2023-02-28/2023-02-28"] =
        some (.fired .value) ∧
      verdict? model2023 (direct "Probe") [direct "Month"] [
        storedCell model2023 1 "2023-03-01/2023-03-01",
        storedCell model2023 5 "02/02"] = some .notFired ∧
      verdict? model2023 (direct "MonthDay") [direct "Probe"] [
        storedCell model2023 6 "02-28/02-28",
        storedCell model2023 1 "2023-02-28/2023-02-28"] =
          some (.fired .value) := by
  native_decide

/- A Base Year completes both lexical spellings of a component set, so the two variants join their slash-separated siblings as admitted fragment operands. -/
example :
    (checkedSource? model2024 (direct "Month") [direct "MonthEmpty"]).isSome = true ∧
      (checkedSource? model2024 (direct "MonthDay")
        [direct "DayMonthDotted"]).isSome = true ∧
      (checkedSource? model2024 (direct "MonthEmpty")
        [direct "MonthDay"]).isSome = true ∧
      (checkedSource? model (direct "Month") [direct "MonthEmpty"]).isNone = true := by
  native_decide

/- A Base Year completes only the yearless operand; the exact operand keeps its own year, so the
same month in another year is disjoint. This is what separates completion to the Base Year from a
year-blind month comparison, and a range spanning into the Base Year still meets the completion. -/
example :
    verdict? model2024 (direct "Probe") [direct "Month"] [
      storedCell model2024 1 "2024-06-01/2024-06-30",
      storedCell model2024 5 "06/06"] = some (.fired .value) ∧
      verdict? model2024 (direct "Probe") [direct "Month"] [
        storedCell model2024 1 "2023-06-01/2023-06-30",
        storedCell model2024 5 "06/06"] = some .notFired ∧
      verdict? model2024 (direct "Probe") [direct "Month"] [
        storedCell model2024 1 "2023-11-01/2024-02-28",
        storedCell model2024 5 "01/01"] = some (.fired .value) := by
  native_decide

/- The completed month-day operand keeps closed endpoints against an exact range, and a leap Base
Year admits its February 29 endpoint. -/
example :
    verdict? model2024 (direct "Probe") [direct "MonthDay"] [
      storedCell model2024 1 "2024-06-30/2024-07-05",
      storedCell model2024 6 "06-01/06-30"] = some (.fired .value) ∧
      verdict? model2024 (direct "Probe") [direct "MonthDay"] [
        storedCell model2024 1 "2024-07-01/2024-07-05",
        storedCell model2024 6 "06-01/06-30"] = some .notFired ∧
      verdict? model2024 (direct "Probe") [direct "MonthDay"] [
        storedCell model2024 1 "2024-02-29/2024-02-29",
        storedCell model2024 6 "02-29/03-05"] = some (.fired .value) := by
  native_decide

/- A year fragment is year-bearing on its own, so it pairs with a completed yearless operand and
its own year decides the outcome. -/
example :
    verdict? model2024 (direct "Year") [direct "Month"] [
      storedCell model2024 3 "2024/2024",
      storedCell model2024 5 "06/06"] = some (.fired .value) ∧
      verdict? model2024 (direct "Year") [direct "Month"] [
        storedCell model2024 3 "2023/2023",
        storedCell model2024 5 "06/06"] = some .notFired := by
  native_decide

private def checkedPluralSource? (checkedModel : FlatModel)
    (scalar first : SurfaceFieldEntityOperand) :
    Option (CheckedAtLeastOneDateRangeOverlapsSource checkedModel) :=
  (elaborateAtLeastOneDateRangeOverlapsSource checkedModel ["Form"] {
    scalar
    list := { first, rest := [] }
  }).toOption

private def pluralVerdict? (checkedModel : FlatModel)
    (scalar first : SurfaceFieldEntityOperand)
    (cells : List ClassifiedCellInput) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler checkedModel).toOption
  let source ← checkedPluralSource? checkedModel scalar first
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption
  (source.evaluateCheckedDocument document []).toOption.map (·.verdict)

/- The plural scan reads a completed fragment on either side, and the exact operand keeps its own
year there too, so the same month in another year is disjoint. -/
example :
    pluralVerdict? model2024 (direct "Probe") (direct "Month") [
      storedCell model2024 1 "2024-06-01/2024-06-30",
      storedCell model2024 5 "06/06"] = some (.fired .value) ∧
      pluralVerdict? model2024 (direct "Month") (direct "Probe") [
        storedCell model2024 5 "06/06",
        storedCell model2024 1 "2024-06-01/2024-06-30"] = some (.fired .value) ∧
      pluralVerdict? model2024 (direct "Probe") (direct "Month") [
        storedCell model2024 1 "2023-06-01/2023-06-30",
        storedCell model2024 5 "06/06"] = some .notFired ∧
      pluralVerdict? model2024 (direct "Probe") (direct "Month") [
        storedCell model2024 1 "2024-03-01/2024-03-31",
        storedCell model2024 5 "06/06"] = some .notFired := by
  native_decide

/- A year fragment scalar decides by its own year, and an unusable scalar leaves the list unread,
so a filled fragment scalar against an empty list is a definite no-fire rather than unknown. -/
example :
    pluralVerdict? model2024 (direct "Year") (direct "Month") [
      storedCell model2024 3 "2024/2024",
      storedCell model2024 5 "06/06"] = some (.fired .value) ∧
      pluralVerdict? model2024 (direct "Year") (direct "Month") [
        storedCell model2024 3 "2023/2023",
        storedCell model2024 5 "06/06"] = some .notFired ∧
      pluralVerdict? model2024 (direct "Month") (direct "Probe") [
        storedCell model2024 5 "06/06"] = some .notFired := by
  native_decide

end A12Kernel.Conformance.DateRangeFragmentOverlap
