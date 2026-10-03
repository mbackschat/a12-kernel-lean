import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ConstructedDateValidityLocks

open A12Kernel A12Kernel.Dm Lean

private def number (id : FieldId) (name : String) (maximum : Rat) : FlatFieldDecl := {
  id, name, groupPath := ["Form"]
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some maximum } }

private def model : FlatModel := {
  timeZoneId := "UTC", baseYear := some 2024
  fields := [number 1 "D" 31, number 2 "M" 12, number 3 "Y" 9999,
    number 4 "C" 99, number 5 "S" 99,
    { id := 6, name := "E", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .string } },
    { id := 7, name := "TextDay", groupPath := ["Form"], policy := { kind := .string }
      stringPolicy := { maxLength := some 2 }, stringPatternSource := some "[0-9]+" },
    { id := 8, name := "Year", groupPath := ["Form"]
      policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy") }
      temporalTargetPolicy := some { format := "yyyy" } },
    { id := 9, name := "Stamp", groupPath := ["Form"]
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def admitted (text : String) : Bool :=
  ((parseText .english text).toOption.bind fun parsed =>
    (lowerCondition model ["Form"] false parsed.body).toOption).isSome

example : ["Valid(Date(D, M, Y))", "Invalid(Date(D, M))",
    "Valid(Date(D, M, C, S))", "Invalid(Date(D, \"02\", \"2024\"))",
    "Valid(Date(D, MonthFromDate(Today), YearFromDate(Now)))",
    "Valid(Date(TextDay, M, Year))",
    "Valid(Date(DayFromDate(Stamp), MonthFromDate(BaseYear), YearFromDate(EndOfDateRange(BaseYear))))"].all admitted := by native_decide

example : ["Valid(Date(D))", "Valid(Date(D, M, Y, C, S))",
    "Valid(Date(D, M, 2024))", "Valid(Date(D, M, \"24\"))",
    "Valid(Date(D, M, MonthFromDate(Today)))", "Valid(Date(Rows*/E, M, Y))"].all
    (fun text => !admitted text) := by native_decide

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def checkedDocument (values : List (String × String)) (rows : Bool := false) :
    Option (CheckedDocument model) := do
  let row := Json.mkObj [("E", "present")]
  let members := (values.map fun (key, value) => (key, Json.str value)) ++
    (if rows then [("Rows", Json.arr #[row, row])] else [])
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj members)])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def runWorlds (text : String) (values : List (String × String))
    (errorPath : String) (times : List Int) (rows : Bool := false) :
    Option (List (List (String × String))) := do
  let rule : DmRule := {
    group := ["Form"], name := "Rule", errorCode := "R"
    errorEntityRelPath := errorPath, condition := text, severity := "ERROR" }
  let document ← checkedDocument values rows
  let checked ← (checkRule dm .english rule { now := { epochMillis := 0 } }).toOption
  times.mapM fun now => do
    let messages ← (runRule { now := { epochMillis := now } } document checked).toOption
    pure (messages.map fun message =>
      let observed := observe model message
      (observed.pointer, observed.messageType))

private def run (text : String) (values : List (String × String))
    (errorPath : String := "../D") : Option (List (String × String)) :=
  (runWorlds text values errorPath [0]).bind List.head?

example : run "Valid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "2024")] =
    some [("Form/D", "VALUE_ERROR")] ∧
    run "Invalid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "2023")] =
      some [("Form/D", "VALUE_ERROR")] ∧
    run "Invalid(Date(D, M, Y))" [] = some [("Form/D", "OMISSION_ERROR")] ∧
    run "Valid(Date(D, M, Y))" [] = some [] ∧
    run "Invalid(Date(D, M, Y))" [("Y", "bad")] = some [] := by native_decide

example : run "Invalid(Date(D, M)) Or FieldFilled(Y)" [("D", "29"), ("M", "2")] = some [] ∧
    run "Valid(Date(D, M, C, S)) And FieldFilled(Y)"
      [("D", "29"), ("M", "2"), ("C", "20"), ("S", "0"), ("Y", "2000")] =
      some [("Form/D", "VALUE_ERROR")] := by native_decide

-- One checked rule is reused: January versus February makes day 30 distinguish runtime clocks.
example : runWorlds "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))"
    [("D", "30")] "../D" [0, 951782400000] = some [[("Form/D", "VALUE_ERROR")], []] ∧
    runWorlds "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now))) And AtLeastOneFieldFilled(Rows*)"
      [("D", "30")] "../Rows/E" [0, 951782400000] true =
      some [[("Form/Rows/E", "VALUE_ERROR")], []] ∧
    runWorlds "FieldFilled(Rows/E) And Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))"
      [("D", "30")] "../Rows/E" [0, 951782400000] true =
      some [[("Form/Rows/E", "VALUE_ERROR"), ("Form/Rows[2]/E", "VALUE_ERROR")], []] := by native_decide

example : run "Valid(Date(TextDay, M, Year))"
    [("TextDay", "29"), ("M", "2"), ("Year", "2024")] "../TextDay" =
      some [("Form/TextDay", "VALUE_ERROR")] ∧
    run "Valid(Date(DayFromDate(Stamp), MonthFromDate(Stamp), YearFromDate(Stamp)))"
      [("Stamp", "2024-02-29")] "../Stamp" = some [("Form/Stamp", "VALUE_ERROR")] := by native_decide

private def references : Option (List FieldId × Bool) := do
  let expression ← (parseText .english "Invalid(Date(D, M, C, S))").toOption
  let condition ← (lowerCondition model ["Form"] false expression.body).toOption
  let pointers ← (condition.core.referencePointers []).toOption
  pure (pointers.map (·.field), condition.core.allLeaves ValidationConditionLeaf.supportsAddressedPartial)

example : references = some ([1, 2, 4, 5], false) := by native_decide

private def leafResult (text : String) (values : List (String × String)) :
    Option (Except CheckedAddressingError Verdict) := do
  let document ← checkedDocument values
  let expression ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false expression.body).toOption
  let .leaf leaf := condition.core | none
  pure (leaf.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document })

example : [leafResult "Valid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "bad")],
    leafResult "Invalid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "bad")]].all
      (fun | some (.ok .unknown) => true | _ => false) = true ∧
    (match leafResult "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))" [("D", "30")] with
      | some (.error (.constructedDate .nowWorldRequired)) => true | _ => false) = true := by native_decide

end A12Kernel.Dm.ConstructedDateValidityLocks
