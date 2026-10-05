import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingCalendarLocks
open Lean A12Kernel HavingFixture

private def dates : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }

example : [("DifferenceInMonths", "12"), ("DifferenceInYears", "1"), ("DifferenceInDays", "366")].all
    (fun (op, expected) => runModel dates s!"{op}(Rows/Tag, $Expected) == {expected}" false
      "2025-03-01" "2024-02-29" "2025-02-28" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : runModel dates "DifferenceInDays($Expected, Rows/Tag) == -366" false
    "2025-03-01" "2024-02-29" "2025-02-28" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInMonths(Rows/Tag, $Expected) == 0" false
      "2025-03-01" "" "2024-02-29" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInYears(Rows/Tag, $Expected) == 0" false
      "2025-03-01" "bad" "2024-02-29" = some (.notFired, []) := by native_decide

private def dateTimes : FlatModel := { dates with timeZoneId := "Europe/Berlin", fields := dates.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss") }
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } else field }

example : runModel dateTimes "DifferenceInDays(Rows/Tag, $Expected) == 1" false
      "2024-03-31T12:00:00" "2024-03-30T12:00:00" "2024-03-31T12:00:00" = some (.fired .omission, ["value 9"]) ∧
    runModel dateTimes "DifferenceInDays(Rows/Tag, $Expected) == 1" false
      "2024-10-27T12:00:00" "2024-10-26T12:00:00" "2024-10-27T12:00:00" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInMonths(Rows/Tag, $Expected) + 1 == 2" false
      "2024-02-29" "2024-01-31" "2024-02-01" = some (.fired .omission, ["value 9"]) := by native_decide

example : ["DifferenceInMonths", "DifferenceInYears"].all (fun op =>
    (runModel dateTimes s!"{op}(Rows/Tag, $Expected) > 0" false
      "2024-03-31T12:00:00" "2024-03-30T12:00:00" "2024-03-31T12:00:00").isNone) = true ∧
    (runModel { dates with timeZoneId := "America/New_York" }
      "DifferenceInDays(Rows/Tag, $Expected) > 0" false "2025-03-01" "2024-02-29" "2025-02-28").isNone = true ∧
    (runModel dates "DifferenceInDays(Rows/Tag, $Expected) == 1.0" false
      "2025-03-01" "2024-02-29" "2025-02-28").isNone = true := by native_decide

example : runModel dates "DifferenceInDays(Rows/Tag, $Expected) == 1" true
    "2025-03-01" "2024-02-29" "2025-02-28" "Date(\"01\", \"03\", \"2024\")" =
      some (.notFired, ["value 2024-03-01", "value 9"]) := by native_decide

private def formatted (left right : String) (baseYear : Option Int := none) : FlatModel := {
  dates with baseYear, fields := dates.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      let format := if field.id == 3 then left else right
      { field with
        policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format } }
    else field }

private def admitted (fixture : FlatModel) (filter : String) : Bool :=
  let expression := "Sum(Rows*/N Having " ++ filter ++ ")"
  ((parseText .english (expression ++ " > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome &&
  (lowerComputation fixture .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).isOk

example : [("DifferenceInMonths", "MM"), ("DifferenceInYears", "MM"), ("DifferenceInDays", "MM-dd")].all
    (fun (op, format) =>
      !admitted (formatted format "yyyy-MM-dd") s!"{op}(Rows/Tag, $Expected) > 0" &&
      admitted (formatted format "yyyy-MM-dd" (some 2024)) s!"{op}(Rows/Tag, $Expected) > 0") = true ∧
    !admitted (formatted "yyyy" "yyyy") "DifferenceInMonths(Rows/Tag, $Expected) > 0" ∧
    !admitted (formatted "yyyy-MM" "yyyy-MM") "DifferenceInDays(Rows/Tag, $Expected) > 0" ∧
    admitted (formatted "yyyy" "yyyy") "DifferenceInYears(Rows/Tag, $Expected) > 0" := by native_decide

example : ["DifferenceInMonths", "DifferenceInYears", "DifferenceInDays"].all (fun op =>
    referencesFor s!"{op}(/Form/Rows/Tag, $/Form/Rows/Tag) == 0"
      { dates with fields := dates.fields ++ [{
        id := 6, name := "Token", groupPath := ["Form", "Rows"]
        repeatableScope := [10], policy := { kind := .string } }] } "Token" == some (true, true) &&
    !admitted dates s!"{op}(Rows*/Tag, $Expected) > 0" &&
    !admitted dates s!"{op}([Rows/Tag], $Expected) > 0" &&
    !admitted dates s!"{op}(Rows/N, $Expected) > 0" &&
    !admitted dates s!"{op}(Rows/Tag, $Out) > 0") = true := by native_decide

end A12Kernel.Dm.HavingCalendarLocks
