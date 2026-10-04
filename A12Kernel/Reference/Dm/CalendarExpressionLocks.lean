import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.CalendarExpressionLocks

private def model : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "D", policy := { kind := .temporal .date TemporalComponents.fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 1, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form"], name := "Result", policy := { kind := .temporal .date TemporalComponents.fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }]
  timeZoneId := "Europe/Berlin", baseYear := some 2024 }

private def admittedIn (model : FlatModel) (operation : String) : Bool :=
  (lowerComputation model .english {
    group := ["Form"], name := "ResultComp", targetRelPath := "../Result"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).isOk

private def admitted := admittedIn model

example : admitted "[D]" = true := by native_decide

-- The calendar-family admission grid keeps the source forms legal across all three units.
example :
    ["AddDays(D,[N])", "AddMonths(D,[N])", "AddYears(D,[N])",
      "AddDays(Today,1)", "AddMonths(Today,1)", "AddYears(Today,1)",
      "Date(DayFromDate(D),MonthFromDate(D),YearFromDate(D))", "Date(\"29\",\"02\",\"20\",\"24\")",
      "AddDays(AddMonths(D,[N]),1)", "AddMonths(AddDays(D,1),[N])"].all admitted = true := by
  native_decide

private def fragmentModel (format : String) (components : TemporalComponents)
    (baseYear : Option Int) : FlatModel :=
  { model with baseYear, fields := model.fields.map fun field =>
      if field.id == 1 then field else { field with
        policy := { kind := .temporal .date components }
        temporalTargetPolicy := some { format } } }

-- The 24 retained static rows cross declared components, calendar unit and Base Year.
example :
    [("yyyy-MM", { TemporalComponents.fullDate with day := false }, [false, true, true]),
     ("MM-dd", { TemporalComponents.fullDate with year := false }, [true, true, false]),
     ("yyyy", { TemporalComponents.fullDate with month := false, day := false }, [false, false, true]),
     ("MM", { TemporalComponents.fullDate with year := false, day := false }, [false, true, false])].all
      (fun (format, components, expected) =>
        ["AddDays(D,1)", "AddMonths(D,1)", "AddYears(D,1)"].map
          (admittedIn (fragmentModel format components none)) == expected &&
        ["AddDays(D,1)", "AddMonths(D,1)", "AddYears(D,1)"].map
          (admittedIn (fragmentModel format components (some 2024))) ==
            [expected[0]!, expected[1]!, true]) = true := by
  native_decide

-- An unavailable calendar era is an implementation fault, not a measured kernel value error.
example :
    (do
      let parsed ← (parseText .english "AddYears(\"01.01.2024\",-3000)").toOption
      let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
      let checked ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
      pure (match checked.evalResult .computation { read := fun _ => malformedCheckedCell } with
        | .error .calendarUnavailable => true | _ => false)) =
      some true := by
  native_decide

private def constructorModel : FlatModel :=
  { model with fields := model.fields ++ [
      { id := 3, groupPath := ["Form"], name := "Y",
        policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy") }
        temporalTargetPolicy := some { format := "yyyy" } }] }

private def extremumGiven (operator constructor : String) : Option Bool := do
  let parsed ← (parseText .english s!"{operator}({constructor},[D])").toOption
  let surface ← (lowerScalarTemporalExpression constructorModel ["Form"] parsed.body).toOption
  let checked ← (elaborateScalarTemporalExpression constructorModel ["Form"] surface).toOption
  let value ← ModelZone.ConcreteProfile.europeBerlin.resolveCompletedDateParts? {
    year := 2024, month := 3, day := 1 }
  let result ← (checked.evalResult .validation {
    read := fun field => checkAdmittedRawCell
      (if field == 0 then .parsed (.temporal (.date value)) else .presentEmpty) }).toOption
  match result with
  | .value _ given => pure given
  | _ => none

-- The review-control grid distinguishes value absence from a missing component for both selectors.
example : ["Min", "Max"].all (fun operator =>
    extremumGiven operator "Date(\"31\",\"02\",\"2024\")" == some true &&
    extremumGiven operator "Date(\"01\",\"01\",Y)" == some false) := by native_decide

private def completedYearGuard (initial : String) : Option (List String) := do
  let model := { constructorModel with fields := constructorModel.fields ++ [
    { id := 4, groupPath := ["Form"], name := "S", policy := { kind := .string } }] }
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Y", Lean.toJson initial), ("N", "9"), ("S", "old")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let define (name target operation : String) (precondition : Option String) : DmComputation := {
    group := ["Form"], name, targetRelPath := target, commonPrecondition := none
    alternatives := [{ precondition, operation }], errorCodesToSuppress := [] }
  let guard := some "Date(\"01\",\"01\",Y) == \"01.01.2024\""
  let steps ← [define "Producer" "../Y" "\"01.01.2024\"" none,
      define "NumberConsumer" "../N" "7" guard,
      define "StringConsumer" "../S" "\"selected\"" guard].mapM fun computation =>
        (lowerComputation model .english computation).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

-- Both consumer kinds must see the completed year's spelling, even when no source spelling exists.
example : completedYearGuard "2023" = some ["value 2024", "value 7", "value selected"] ∧
    completedYearGuard "" = some ["value 2024", "value 7", "value selected"] := by native_decide

end A12Kernel.Dm.CalendarExpressionLocks
