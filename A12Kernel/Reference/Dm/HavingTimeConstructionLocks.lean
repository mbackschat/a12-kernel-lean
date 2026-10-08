import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingTimeConstructionLocks
open Lean A12Kernel

private def model : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maxStoredLength := some 2 } } else field }
private def run (filter selected : String) (first : String := "8") (second : String := "9")
    (fixture : FlatModel := model) (fresh : Bool := false) (producer : String := "9") :=
  HavingFixture.runModel fixture filter fresh "8" first second producer (ruleExpected := selected)
    (zoneRules := ModelZone.concreteRules)

example : run "Time(Rows/Tag) == \"08:00:00\"" "9" =
    some (.fired .omission, ["value 9"]) := by native_decide

private def stringModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .string }, numericTargetConstraints := {}
    stringPolicy := { maxLength := some 2 }, stringPatternSource := some "[0-9]+" } else field }
private def clockModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .date TemporalComponents.time }, numericTargetConstraints := {}
    temporalTargetPolicy := some { format := "HH:mm:ss" } } else field }
example : run "Time(Rows/Tag) == \"08:00:00\"" "9" (fixture := stringModel) =
      some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel clockModel "Time(HoursFromTime(Rows/Tag)) == \"08:00:00\"" false
      "08:30:45" "08:30:45" "09:40:55" (ruleExpected := "9") (zoneRules := ModelZone.concreteRules) =
      some (.fired .omission, ["value 9"]) ∧
    run "Time(HoursFromTime(Now)) == \"00:00:00\" And FieldFilled(Rows/N)" "14" =
      some (.fired .omission, ["value 14"]) := by native_decide

example : [("Time()", "00:00:00"), ("Time(\"00000008\")", "08:00:00"),
    ("Time(\"0008\",\"000030\")", "08:30:00"),
    ("Time(\"0008\",\"000030\",\"000045\")", "08:30:45")].all (fun (source, expected) =>
      run (source ++ " == \"" ++ expected ++ "\" And FieldFilled(Rows/N)") "14" ==
        some (.fired .omission, ["value 14"])) = true ∧
    [model, stringModel].all (fun fixture =>
      [("Time(Rows/Tag)", "08:00:00"), ("Time(Rows/Tag,\"30\")", "08:30:00"),
        ("Time(Rows/Tag,\"30\",\"45\")", "08:30:45")].all fun (source, expected) =>
          run (source ++ " == \"" ++ expected ++ "\"") "9" (fixture := fixture) ==
            some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["\"08:00:00\" == Time(Rows/Tag)", "Time(Rows/Tag) == Time($Expected)",
    "Time($Expected) == Time(Rows/Tag)", "Time(Rows/Tag) < \"09:00:00\"",
    "\"09:00:00\" > Time(Rows/Tag)", "Time(Rows/Tag,$Expected,$Expected) == \"08:08:08\""].all
      (fun filter => run filter "9" == some (.fired .omission, ["value 9"])) = true ∧
    run "DateTime(\"12.04.2024\",Time(Rows/Tag,\"30\",\"45\")) == \"12.04.2024T08:30:45\"" "9" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : [("HoursFromTime", "8", "9"), ("MinutesFromTime", "30", "14"),
    ("SecondsFromTime", "45", "14")].all (fun (operator, amount, selected) =>
      run (operator ++ "(Time(Rows/Tag,\"30\",\"45\")) + 1 == " ++ amount ++ " + 1") selected ==
        some (.fired .omission, ["value " ++ selected])) = true ∧
    ["", "24"].all (fun missingOrUnreal =>
      run "HoursFromTime(Time(Rows/Tag)) == 0" "9" missingOrUnreal == some (.fired .omission, ["value 9"]) &&
      run "Time(Rows/Tag) == \"08:00:00\"" "0" missingOrUnreal == some (.fired .omission, ["value 0"])) = true ∧
    run "Time(Rows/Tag) == \"09:00:00\"" "5" "bad" = some (.fired .omission, []) ∧
    run "Time(Rows/Tag) == \"09:00:00\"" "5" "ab" (fixture := stringModel) =
      some (.fired .omission, []) := by native_decide

private def clockRun (filter selected : String) :=
  HavingFixture.runModel clockModel filter false "08:30:45" "08:30:45" "09:40:55"
    (ruleExpected := selected) (zoneRules := ModelZone.concreteRules)
private def clockConstruction := "Time(HoursFromTime(Rows/Tag),MinutesFromTime(Rows/Tag),SecondsFromTime(Rows/Tag))"
example : clockRun (clockConstruction ++ " == \"08:30:45\"") "9" =
      some (.fired .omission, ["value 9"]) ∧
    clockRun "Time(\"08\",MinutesFromTime(Rows/Tag)) == \"08:30:00\"" "9" =
      some (.fired .omission, ["value 9"]) ∧
    clockRun "Time(\"08\",\"30\",SecondsFromTime(Rows/Tag)) == \"08:30:45\"" "9" =
      some (.fired .omission, ["value 9"]) ∧
    [("HoursFromTime", "8"), ("MinutesFromTime", "30"), ("SecondsFromTime", "45")].all
      (fun (operator, amount) => clockRun (operator ++ "(" ++ clockConstruction ++ ") == " ++ amount) "9" ==
        some (.fired .omission, ["value 9"])) = true := by native_decide

example : [("UTC", "00:00:00"), ("Europe/Berlin", "01:00:00")].all (fun (zone, expected) =>
    run ("Time(HoursFromTime(Now),MinutesFromTime(Now),SecondsFromTime(Now)) == \"" ++ expected ++
      "\" And FieldFilled(Rows/N)") "14" (fixture := { model with timeZoneId := zone }) ==
        some (.fired .omission, ["value 14"])) = true := by native_decide

private def pointerModel : FlatModel := { model with
  fields := model.fields ++ [{
    id := 6, name := "Token", groupPath := ["Form", "Rows"]
    repeatableScope := [10], policy := { kind := .string } }] }
example : HavingFixture.referencesFor "Time(/Form/Rows/Tag) == Time($/Form/Rows/Tag)"
      pointerModel "Token" = some (true, true) ∧
    HavingFixture.referencesFor "Time(/Form/Rows/Tag) == \"08:00:00\""
      pointerModel "Token" = some (true, false) ∧
    run "Time(Rows/Tag) == Time($Expected)" "9" (fresh := true) =
      some (.fired .omission, ["value 9", "value 5"]) := by native_decide

private def accepted (filter : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ ") > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome
example : accepted "Time(Rows/Tag) == \"08:00:00\"" = true ∧
    ["Time(\"08\",\"30\",\"45\",\"00\")", "Time(8)", "Time(Rows/Tag + 1)",
      "Time([Rows/Tag])", "Time({Rows/Tag})", "Time(Rows/Tag For \"k\")", "Time(Rows*/Tag)",
      "Time(\"-1\")", "Time(\"1.5\")", "Time(\"24\")", "Time(\"08\",\"60\")", "Time(\"08\",\"30\",\"60\")",
      "Time(HoursFromTime(Time(Rows/Tag)))"].all
      (fun source => !accepted (source ++ " == \"08:00:00\"")) = true ∧
    ["Time(MinutesFromTime(Rows/Tag))", "Time(\"08\",HoursFromTime(Rows/Tag))",
      "Time(\"08\",\"30\",MinutesFromTime(Rows/Tag))", "Time(Rows/Tag)"].all
      (fun source => !accepted (source ++ " == \"08:00:00\"") clockModel) = true ∧
    accepted (clockConstruction ++ " == \"08:30:45\"") clockModel = true ∧
    accepted "Time($Expected) == \"08:00:00\"" = false ∧
    accepted "Time($Rows/Tag) == Time($Expected)" = false := by native_decide

private def numericModel (constraints : NumericTargetConstraints) (info : NumField := { scale := 0, signed := false }) : FlatModel :=
  { model with fields := model.fields.map fun field => if field.id == 3 then { field with
    policy := { kind := .number info }, numericTargetConstraints := constraints } else field }
example : run "Time(Rows/Tag) == \"08:00:00\"" "9" (fixture := numericModel { maximum := some 23 }) =
      some (.fired .omission, ["value 9"]) ∧
    run "Time(\"08\",Rows/Tag) == \"08:08:00\"" "9" (fixture := numericModel { maximum := some 59 }) =
      some (.fired .omission, ["value 9"]) ∧
    run "Time(\"08\",\"30\",Rows/Tag) == \"08:30:08\"" "9" (fixture := numericModel { maximum := some 59 }) =
      some (.fired .omission, ["value 9"]) ∧
    run "Time(Rows/Tag) == \"08:00:00\"" "9"
      (fixture := numericModel { minimum := some 0, maximum := some 23 } { scale := 0, signed := true }) =
        some (.fired .omission, ["value 9"]) ∧
    [numericModel { maxIntegerDigits := some 2 }, numericModel { maximum := some 59 },
      numericModel { maxStoredLength := some 2 } { scale := 1, signed := false },
      numericModel { maxStoredLength := some 2, minFractionalDigits := 1 },
      numericModel { maxStoredLength := some 2 } { scale := 0, signed := true },
      numericModel { maxStoredLength := some 2, minimum := some (-1) } { scale := 0, signed := true }].all
      (fun fixture => !accepted "Time(Rows/Tag) == \"08:00:00\"" fixture) = true ∧
    accepted "Time(\"08\",Rows/Tag) == \"08:08:00\"" (numericModel { maximum := some 23 }) = false := by native_decide

private def patterned (pattern : String) (maximum : Nat := 2) : FlatModel := { stringModel with
  fields := stringModel.fields.map fun field => if field.id == 2 || field.id == 3 then { field with
    stringPolicy := { maxLength := some maximum }, stringPatternSource := some pattern } else field }
private def extensible : FlatModel := { stringModel with
  fields := stringModel.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with stringExtensibleEnum := true, stringPatternSource := none } else field }
example : ["[0-9]+", "[0-9]*", "\\d+", "\\d*", "[0-9]{2}", "\\d{2}"].all (fun pattern =>
    accepted "Time(Rows/Tag) == \"08:00:00\"" (patterned pattern)) = true ∧
    accepted "Time(Rows/Tag) == \"08:00:00\"" (patterned "[0-9]{1,2}") = false ∧
    accepted "Time(Rows/Tag) == \"08:00:00\"" (patterned "[0-9]+" 3) = false ∧
    run "Time(Rows/Tag) == \"08:00:00\"" "9" (fixture := extensible) =
      some (.fired .omission, ["value 9"]) ∧
    accepted "Time(Rows/Tag) == \"08:00:00\"" extensible = true ∧
    run "Time(Rows/Tag) == \"08:00:00\"" "9" "ab" (fixture := extensible) = some (.fired .value, []) := by native_decide

private def wrongStringKind (enumerated : Bool) : FlatModel := { stringModel with
  fields := stringModel.fields.map fun field => if field.id == 3 then
    if enumerated then { field with
      policy := { kind := .enumeration }
      enumeration := some { storedTokens := ["8", "9"] }, stringPolicy := {}, stringPatternSource := none }
    else { field with customType := some { name := "Code" } } else field }
example : [false, true].all (fun enumerated =>
    !accepted "Time(Rows/Tag) == \"08:00:00\"" (wrongStringKind enumerated)) = true := by native_decide

end A12Kernel.Dm.HavingTimeConstructionLocks
