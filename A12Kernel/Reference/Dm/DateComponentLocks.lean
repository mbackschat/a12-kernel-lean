import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.DateComponentLocks

private def model : FlatModel :=
  let number (id : FieldId) (name : String) (width : Nat) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maxStoredLength := some width } }
  let text (id : FieldId) (name : String) (width : Nat) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .string }, stringPolicy := { maxLength := some width }
    stringPatternSource := some "[0-9]+" }
  let date (id : FieldId) (name : String) (format : String) (components : TemporalComponents)
      (partialMode : TemporalPartialMode := .full) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .temporal .date components }, temporalTargetPolicy := some { format, partialMode } }
  { fields := [
      { id := 0, name := "Out", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate }
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 2, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      { id := 3, name := "After", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } } },
      number 4 "Day" 2, number 5 "Month" 2, number 6 "Year" 4, number 7 "Century" 2, number 8 "ShortYear" 2,
      text 9 "DayText" 2, text 11 "MonthText" 2, text 12 "YearText" 4,
      date 13 "YearDate" "yyyy" { year := true, month := false, day := false, hour := false, minute := false, second := false },
      date 14 "Full" "yyyy-MM-dd" .fullDate,
      date 15 "Partial" "yyyy-MM-dd" .fullDate .yearOptional ]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 2 }]
    baseYear := some 2024, timeZoneId := "UTC" }

private structure Scenario where
  key : String := "B"
  duplicate : Bool := false
  selected : List (String × String) := []
  keyProducer : Bool := false

private def input (scenario : Scenario) : Lean.Json :=
  let row (code day month year full partialText : String) (overrides : List (String × String)) :=
    Lean.Json.mkObj (([("Code", code), ("Day", day), ("Month", month), ("Year", year),
      ("Century", "20"), ("ShortYear", "24"), ("DayText", day), ("MonthText", month),
      ("YearText", year), ("YearDate", year), ("Full", full), ("Partial", partialText)].map fun (name, value) =>
        (name, Lean.Json.str ((overrides.lookup name).getD value))))
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "2001-12-25"), ("After", .str "9"), ("Key", .str scenario.key),
    ("Rows", .arr #[row (if scenario.duplicate then "B" else "A") "01" "01" "2023" "2023-01-01" "2023-01-00" [],
      row "B" "29" "02" "2024" "2024-02-29" "2024-02-00" scenario.selected])])]

private def checked (scenario : Scenario) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def run (source : String) (scenario : Scenario := {}) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked scenario
  let steps ← ([("After", "1", some "FieldNotFilled(Out)"), ("Out", source, none)] ++
    (if scenario.keyProducer then [("Key", "\"B\"", none)] else [])).mapM fun (target, operation, guard) =>
      (lowerComputation model .english {
        name := target ++ "Comp", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := guard, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document (steps.map (·.2))).toOption
  pure ((results.filter (fun result => !result.pointer.endsWith "/Key")).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

private def validate (source : String) (scenario : Scenario := {}) : Option Verdict := do
  let document ← checked scenario
  let parsed ← (parseText .english source).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).toOption

private def constructed := [
  "Date(Rows/Day For Key,Rows/Month For Key,Rows/Year For Key)",
  "Date(Rows/Day For Key,Rows/Month For Key)",
  "Date(Rows/Day For Key,Rows/Month For Key,Rows/Century For Key,Rows/ShortYear For Key)",
  "Date(Rows/DayText For Key,Rows/MonthText For Key,Rows/YearText For Key)",
  "Date(DayFromDate(Rows/Full For Key),MonthFromDate(Rows/Full For Key),YearFromDate(Rows/Full For Key))"]

example : constructed.all (fun source =>
    run source == some ["Form/After:cleared", "Form/Out:value 2024-02-29"] &&
    validate (source ++ " == \"29.02.2024\"") == some (.fired .value) &&
    run source { key := "missing", keyProducer := true } == some ["Form/After:cleared", "Form/Out:value 2024-02-29"]) = true := by native_decide

example : run "Date(\"1\",\"2\",Rows/YearDate For Key)" =
    some ["Form/After:cleared", "Form/Out:value 2024-02-01"] ∧
    run "Date(DayFromDate(AddDays(Rows/Full For Key,1)),MonthFromDate(AddDays(Rows/Full For Key,1)),YearFromDate(AddDays(Rows/Full For Key,1)))" =
    some ["Form/After:cleared", "Form/Out:value 2024-03-01"] := by native_decide

private def interpreted := "Date(\"1\",\"2\",YearFromDate(AddDays(ValueAsDate(Rows/Partial For Key,FirstDay),1)))"

example : run interpreted = some ["Form/After:cleared", "Form/Out:value 2024-02-01"] ∧
    run ("Min(" ++ interpreted ++ ",\"15.02.2024\")") { selected := [("Partial", "0000-00-00")] } =
      some ["Form/After:value 1", "Form/Out:cleared"] ∧
    run "Date(DayFromDate(AddDays(ValueAsDate(Rows/Partial For Key,FirstDay),1)),Rows/Month For Key,Rows/Year For Key)"
      { selected := [("Partial", "0000-00-00"), ("Month", "bad")] } =
      some ["Form/After:cleared", "Form/Out:cleared"] := by native_decide

example : constructed.all (fun source =>
    run source { key := "missing" } == some ["Form/After:value 1", "Form/Out:cleared"] &&
    run source { duplicate := true } == some ["Form/After:cleared", "Form/Out:cleared"]) = true := by native_decide

example : ["Date(MonthFromDate(Rows/Full For Key),\"2\",\"2024\")",
    "Date(\"1\",\"2\",YearFromDate(Rows/Full For Key),\"24\")",
    "Date([Rows/Day For Key]+1,\"2\",\"2024\")",
    "Date(\"1\",\"2\",YearFromDate(ValueAsDate(Rows/Partial For Key,FirstDay)))"].all
    (fun source => (run source).isNone) = true := by native_decide

example : [("Day", constructed[0]!), ("DayText", constructed[3]!)].all (fun (field, source) =>
    run source { selected := [(field, "")] } == some ["Form/After:value 1", "Form/Out:cleared"] &&
    run source { selected := [(field, "bad")] } == some ["Form/After:cleared", "Form/Out:cleared"] &&
    run source { selected := [(field, "31")] } == some ["Form/After:value 1", "Form/Out:cleared"]) = true := by native_decide

example : constructed.all (fun source =>
    validate (source ++ " == \"29.02.2024\"") { key := "missing" } == some .notFired &&
    validate (source ++ " == \"29.02.2024\"") { duplicate := true } == some .unknown) = true := by native_decide

example : validate "Date(DayFromDate(AddDays(Out,1)),MonthFromDate(AddDays(Out,1)),YearFromDate(AddDays(Out,1))) == \"26.12.2001\"" =
    some (.fired .value) := by native_decide

private def currentSelectedDay : Option DateParts := do
  let document ← checked {}
  let parsed ← (parseText .english constructed[0]!).toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  let expression ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
  if !(expression.referencesField 1 && expression.referencesField 2 && expression.referencesField 4 &&
      expression.referencesField 5 && expression.referencesField 6 && expression.requiresAddressed &&
      expression.bindingScopes.all List.isEmpty) then none else pure ()
  let context := document.indexedScalarComputationContext { now := { epochMillis := 0 } }
  let some addressed := context.addressed | none
  let current := { addressed with
    read := fun row field => if row == [(10,2)] && field == 4 then
      checkAdmittedRawCell (.parsed (.num 1)) else addressed.read row field }
  let .value (.date value) true ← (expression.evalResult .computation
    { read := context.read, storedText := context.storedText, world := context.world } (some current)).toOption | none
  pure value.parts

example : currentSelectedDay = some { year := 2024, month := 2, day := 1 } := by native_decide

end A12Kernel.Dm.DateComponentLocks
