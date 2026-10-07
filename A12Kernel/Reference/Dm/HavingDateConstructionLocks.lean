import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingDateConstructionLocks
open Lean A12Kernel

private def number (id : FieldId) (name : String) (maximum : Rat) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maximum := some maximum } }
private def model : FlatModel := { HavingFixture.model with
  timeZoneId := "UTC", baseYear := some 2024
  fields := HavingFixture.model.fields ++ [
    number 6 "Day" 31, number 7 "Month" 12, number 8 "YearNumber" 9999,
    number 9 "Century" 99, number 10 "ShortYear" 99,
    { (number 11 "OuterYear" 9999) with groupPath := ["Form"], repeatableScope := [] },
    { id := 12, name := "TextD", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 }
      stringPatternSource := some "[0-9]+" },
    { id := 13, name := "Year", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .temporal .time (TemporalComponents.ofFormat "yyyy") }
      temporalTargetPolicy := some { format := "yyyy" } },
    { id := 14, name := "Stamp", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .temporal .time TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }] }

private def run (filter selected : String) (fixture : FlatModel := model)
    (firstDay : String := "29") (secondDay : String := "30") (thirdDay : String := "")
    (outerYear : String := "2024") (stamp : String := "2024-02-29")
    (fresh : Bool := false) (producer : String := "\"drop\"") : Option (Verdict × List String) :=
  let row (n day : String) := Json.mkObj [
    ("N", .str n), ("Day", .str day), ("Month", .str "2"), ("YearNumber", .str "2024"),
    ("Century", .str "20"), ("ShortYear", .str "24"), ("TextD", .str day),
    ("Year", .str "2024"), ("Stamp", .str stamp)]
  HavingFixture.runModel fixture filter fresh outerYear "" "" producer (ruleExpected := selected)
    (zoneRules := ModelZone.concreteRules) (extra := [("OuterYear", .str outerYear)])
    (rowsOverride := some #[row "2" firstDay, row "5" secondDay, row "7" thirdDay])

example : run "Date(Rows/Day,\"02\",\"2024\") == \"29.02.2024\"" "2" =
    some (.fired .omission, ["value 2"]) := by native_decide

example : run "{Date(Rows/Day,\"02\",\"2024\")} == \"29.02.2024\"" "2" =
    some (.fired .omission, ["value 2"]) := by native_decide

private def sources := ["Date(Rows/Day,\"02\")", "Date(Rows/Day,\"02\",\"2024\")",
  "Date(Rows/Day,\"02\",\"20\",\"24\")", "Date(Rows/Day,Rows/Month,Rows/YearNumber)",
  "Date(Rows/Day,Rows/Month,Rows/Century,Rows/ShortYear)", "Date(Rows/TextD,Rows/Month,Rows/Year)",
  "Date(Rows/Day,\"02\",$OuterYear)"]
example : sources.all (fun source => [false, true].all fun reverse =>
    run (if reverse then "\"29.02.2024\" == " ++ source else source ++ " == \"29.02.2024\"") "2" ==
      some (.fired .omission, ["value 2"])) = true ∧
    run "Date(Rows/Day,\"02\",\"2024\") < \"01.03.2024\"" "2" =
      some (.fired .omission, ["value 2"]) ∧
    run "\"01.03.2024\" > Date(Rows/Day,\"02\",\"2024\")" "2" =
      some (.fired .omission, ["value 2"]) := by native_decide

example : run "DateTime(Date(Rows/Day,\"02\",\"2024\"),\"12:30:00\") == \"29.02.2024T12:30:00\"" "2" =
      some (.fired .omission, ["value 2"]) ∧
    [("DayFromDate", "29"), ("MonthFromDate", "2"), ("QuarterFromDate", "1"), ("YearFromDate", "2024")].all
      (fun (operator, expected) => run (operator ++ "(Date(Rows/Day,\"02\",\"2024\")) == " ++ expected) "2" ==
        some (.fired .omission, ["value 2"])) = true ∧
    run "YearFromDate(DateFromDateTime(DateTime(Date(Rows/Day,\"02\",\"2024\"),\"12:30:00\"))) + [Rows/N] == 2026" "2" =
      some (.fired .omission, ["value 2"]) := by native_decide

example : run "YearFromDate(Date(Rows/Day,\"02\",\"2024\")) == 0" "12" =
      some (.fired .omission, ["value 12"]) ∧
    run "YearFromDate(Date(Rows/Day,\"02\",\"2024\")) == 0" "7" (secondDay := "29") =
      some (.fired .omission, ["value 7"]) ∧
    run "YearFromDate(Date(Rows/Day,\"02\",\"2024\")) == 0" "5" (thirdDay := "29") =
      some (.fired .omission, ["value 5"]) ∧
    run "Date(Rows/Day,\"02\",\"2024\") == \"29.02.2024\"" "5" (firstDay := "bad") (secondDay := "29") =
      some (.fired .omission, []) ∧
    run "DayFromDate(Date(Rows/TextD,\"02\",\"2024\")) == 29" "5" (firstDay := "bad") (secondDay := "29") =
      some (.fired .omission, []) := by native_decide

example : run "Date(DayFromDate(Rows/Stamp),MonthFromDate(Rows/Stamp),YearFromDate(Rows/Stamp)) == \"29.02.2024\" And FieldFilled(Rows/N)" "14" =
      some (.fired .omission, ["value 14"]) ∧
    run "Date(\"29\",\"02\",\"2024\") == \"29.02.2024\" And FieldFilled(Rows/N)" "14" =
      some (.fired .omission, ["value 14"]) ∧
    run "Date(Rows/Day,MonthFromDate(Today),YearFromDate(Now)) == \"29.01.1970\"" "2" =
      some (.fired .omission, ["value 2"]) ∧
    run "Date(Rows/Day,MonthFromDate(EndOfDateRange(BaseYear)),YearFromDate(BaseYear)) == \"29.12.2024\"" "2" =
      some (.fired .omission, ["value 2"]) := by native_decide

example : run "DayFromDate(Date(\"29\",\"02\",$OuterYear)) == 29 And FieldFilled(Rows/N)" "14" (outerYear := "1500") =
    some (.fired .omission, ["value 14"]) := by native_decide

private def accepted (filter : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ ") > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome
example : accepted "Date(Rows/Day,\"02\") == \"29.02.2024\"" = true ∧
    accepted "Date(Rows/Day,\"02\") == \"29.02.2024\"" { model with baseYear := none } = false ∧
    run "Date(Rows/Day,\"02\",\"2024\") == \"29.02.2024\"" "2" { model with baseYear := none } =
      some (.fired .omission, ["value 2"]) ∧
    ["Valid", "Invalid"].all (fun operator =>
      !accepted (operator ++ "(Date(\"29\",\"02\",\"2024\")) And FieldFilled(Rows/N)") &&
      !accepted (operator ++ "(Date(DayFromDate(Rows/Stamp),MonthFromDate(Rows/Stamp),YearFromDate(Rows/Stamp))) And FieldFilled(Rows/N)")) = true ∧
    accepted "Valid(Date(Rows/Day,Rows/Month,Rows/YearNumber))" = true := by native_decide

private def pointerModel : FlatModel := { model with
  fields := (model.fields.map fun field => if field.id == 3 then { (number 3 "Tag" 31) with
    groupPath := field.groupPath, repeatableScope := field.repeatableScope } else field) ++ [{
      id := 15, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }
example : HavingFixture.referencesFor
      "Date(/Form/Rows/Tag,\"02\",\"2024\") == Date($/Form/Rows/Tag,\"02\",\"2024\")"
      pointerModel "Token" = some (true, true) ∧
    HavingFixture.referencesFor "Date(/Form/Rows/Tag,\"02\",\"2024\") == \"29.02.2024\""
      pointerModel "Token" = some (true, false) := by native_decide

example : HavingFixture.referencesFor
    "Date(/Form/Rows/Tag,\"02\",\"2024\") == Date($/Form/Rows/Tag,\"02\",\"2024\")"
    { pointerModel with fields := pointerModel.fields.map fun field => if field.id == 3 then { field with
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 }
      numericTargetConstraints := {}, stringPatternSource := some "[0-9]+" } else field } "Token" = some (true, true) ∧
    run "Date(Rows/TextD,Rows/Month,Rows/Year) == \"29.02.2024\"" "2"
      { model with fields := model.fields.map fun field => if field.id == 12 then { field with
        stringPatternSource := none, stringExtensibleEnum := true } else field } =
      some (.fired .omission, ["value 2"]) := by native_decide

private def freshModel : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 2 then { (number 2 "Expected" 9999) with
    groupPath := ["Form"], repeatableScope := [] } else field }
example : run "Date(Rows/Day,\"02\",$Expected) == \"29.02.2024\"" "2" freshModel
    (fresh := true) (producer := "2023") = some (.fired .omission, ["value 2023", "value 0"]) := by native_decide

example : ["Date(Rows/Day)", "Date(Rows/Day,\"02\",\"20\",\"24\",\"1\")",
    "Date([Rows/Day],\"02\",\"2024\")", "Date({Rows/Day},\"02\",\"2024\")",
    "Date(Rows/Day For \"k\",\"02\",\"2024\")", "Date(Rows*/Day,\"02\",\"2024\")",
    "Date(Rows/Tag,\"02\",\"2024\")", "Date(Rows/Year,\"02\",\"2024\")",
    "Date(Rows/Day,Rows/Day,\"2024\")", "Date(Rows/Day,\"02\",MonthFromDate(Rows/Stamp))",
    "Date(\"32\",Rows/Month,\"2024\")", "Date(Rows/Day,\"13\",\"2024\")",
    "Date(Rows/Day,\"02\",\"24\")", "Date(Rows/Day,2,\"2024\")",
    "Date(DayFromDate(Date(Rows/Day,\"02\",\"2024\")),\"02\",\"2024\")"].all
      (fun source => !accepted (source ++ " == \"29.02.2024\"")) = true := by native_decide

private def alteredNumber (signed : Bool) (scale : Nat) (maximum : Rat) : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 6 then { field with
    policy := { kind := .number { scale, signed } }
    numericTargetConstraints := { maximum := some maximum } } else field }
example : [(true, 0, 31), (false, 1, 31), (false, 0, 32)].all (fun (signed, scale, maximum) =>
    !accepted "Date(Rows/Day,\"02\",\"2024\") == \"29.02.2024\"" (alteredNumber signed scale maximum)) = true ∧
    accepted "Date(Rows/TextD,Rows/Month,Rows/Year) == \"29.02.2024\"" = true ∧
    accepted "Date(Rows/TextD,Rows/Month,Rows/Year) == \"29.02.2024\""
      { model with fields := model.fields.map fun field => if field.id == 12 then
        { field with stringPolicy := { maxLength := some 3 } } else field } = false := by native_decide

private def partialModel (mode : TemporalPartialMode) : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 14 then { field with
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := mode } } else field }
example : run "Date(Rows/Day,MonthFromDate(Rows/Stamp),Rows/YearNumber) == \"29.02.2024\"" "2"
      (partialModel .dayOptional) (stamp := "2024-02-00") = some (.fired .omission, ["value 2"]) ∧
    run "Date(Rows/Day,Rows/Month,YearFromDate(Rows/Stamp)) == \"29.02.2024\"" "2"
      (partialModel .monthOptional) (stamp := "2024-00-00") = some (.fired .omission, ["value 2"]) ∧
    accepted "Date(DayFromDate(Rows/Stamp),Rows/Month,Rows/YearNumber) == \"29.02.2024\""
      (partialModel .dayOptional) = false ∧
    accepted "Date(Rows/Day,MonthFromDate(Rows/Stamp),Rows/YearNumber) == \"29.02.2024\""
      (partialModel .monthOptional) = false := by native_decide

end A12Kernel.Dm.HavingDateConstructionLocks
