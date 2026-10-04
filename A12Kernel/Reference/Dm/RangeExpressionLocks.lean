import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.RangeExpressionLocks

private def model (format : String) (baseYear : Option Int := none) : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "Range", policy := { kind := .dateRange },
      dateRangePolicy := some { format, separator := "/" } },
    { id := 1, groupPath := ["Form"], name := "Result",
      policy := { kind := .temporal .date (TemporalComponents.ofFormat
        (if (TemporalComponents.ofFormat format).year || baseYear.isSome then "yyyy-MM-dd" else "MM-dd")) },
      temporalTargetPolicy := some { format :=
        if (TemporalComponents.ofFormat format).year || baseYear.isSome then "yyyy-MM-dd" else "MM-dd" } }]
  timeZoneId := "UTC", baseYear }

private def admitted (model : FlatModel) (operation : String) : Bool :=
  (lowerComputation model .english {
    group := ["Form"], name := "ResultComp", targetRelPath := "../Result"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).isOk

-- KF201 separates extraction from the consuming format gate; all five profiles reach both bounds.
example : ["yyyy-MM-dd", "yyyy", "yyyy-MM", "MM", "MM-dd"].all (fun format =>
    [none, some 2024].all (fun year =>
      ["StartOfDateRange(Range)", "EndOfDateRange(Range)",
       "Max(StartOfDateRange(Range),EndOfDateRange(Range))"].all
        (admitted (model format year)))) := by native_decide

example : admitted (model "yyyy" (some 2024)) "EndOfDateRange(BaseYear)" := by native_decide

private def comparisonAdmitted (model : FlatModel) (condition : String) : Bool :=
  match parseText .english condition with
  | .ok parsed => (lowerCondition model ["Form"] false parsed.body).isOk
  | .error _ => false

-- The static grid separates entity syntax, range kind, Base Year and consumer component gates.
example : ["StartOfDateRange", "EndOfDateRange"].all (fun op =>
    [none, some 2024].all (fun year =>
      let m := model "MM" year
      comparisonAdmitted m s!"{op}(Range) == [Result]" &&
      !comparisonAdmitted m s!"{op}([Range]) == [Result]" &&
      !comparisonAdmitted m s!"{op}(Result) == [Result]" &&
      !comparisonAdmitted m s!"AddDays({op}(Range),1) > [Result]" &&
      comparisonAdmitted m s!"AddMonths({op}(Range),1) > [Result]" &&
      (comparisonAdmitted m s!"{op}(BaseYear) == [Result]" == year.isSome))) := by
  native_decide

private def run (format : String) (year : Option Int) (text operation : String) : Option String := do
  let model := model format year
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Range", Lean.toJson text), ("Result", Lean.toJson
      (if (TemporalComponents.ofFormat format).year || year.isSome then "2001-12-25" else "12-25"))])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let (_, step) ← (lowerComputation model .english {
    group := ["Form"], name := "ResultComp", targetRelPath := "../Result"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).toOption
  pure (← (← (runComputations world prepared checked [step]).toOption).head?).outcome

-- Both endpoints keep positional completion rather than reusing a field's earliest-date default.
example :
    run "yyyy" none "2023/2024" "StartOfDateRange(Range)" = some "value 2023-01-01" ∧
    run "yyyy" none "2023/2024" "EndOfDateRange(Range)" = some "value 2024-12-31" ∧
    run "MM" none "01/02" "EndOfDateRange(Range)" = some "value 02-29" ∧
    run "MM" (some 2023) "01/02" "EndOfDateRange(Range)" = some "value 2023-02-28" ∧
    run "MM" (some 2024) "01/02" "EndOfDateRange(Range)" = some "value 2024-02-29" := by
  native_decide

example : run "yyyy" none "" "EndOfDateRange(Range)" = some "cleared" := by native_decide

-- Dependency omission would let a consumer run before its range producer or admit a target self-read.
example :
    (do
      let parsed ← (parseText .english "Max(StartOfDateRange(Range),EndOfDateRange(Range))").toOption
      let surface ← (lowerScalarTemporalExpression (model "yyyy") ["Form"] parsed.body).toOption
      let checked ← (elaborateScalarTemporalExpression (model "yyyy") ["Form"] surface).toOption
      pure checked.fieldIds) = some [0, 0] := by native_decide

end A12Kernel.Dm.RangeExpressionLocks
