import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Elaboration.ValidationCondition.Reference
import A12Kernel.Semantics.MessageIndex

namespace A12Kernel.Dm.SelectedMessageLocks

private def model : FlatModel := {
  timeZoneId := "UTC"
  fields := [
    { id := 1, name := "Key", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .string } },
    { id := 2, name := "Anchor", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Id", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .string } },
    { id := 4, name := "N", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Text", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .string } },
    { id := 6, name := "Flag", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .boolean } },
    { id := 7, name := "Stamp", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 8, name := "A", groupPath := ["Form", "Parents", "Rows", "Body"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "B", groupPath := ["Form", "Parents", "Rows", "Body"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, name := "N", groupPath := ["Form", "Parents", "Rows", "Items"], repeatableScope := [1, 10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 11, name := "M", groupPath := ["Form", "Parents", "Rows", "Items"], repeatableScope := [1, 10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 12, name := "Fallback", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .boolean } },
    { id := 13, name := "Day", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 2 } },
    { id := 14, name := "Stamp", groupPath := ["Form", "Parents", "Rows", "Items"], repeatableScope := [1, 10, 20], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 15, name := "LookupKey", groupPath := ["Form", "Parents", "Lookup"], repeatableScope := [1, 30], policy := { kind := .string } }]
  repeatableGroups := [
    { level := 1, path := ["Form", "Parents"], repeatability := some 2 },
    { level := 10, path := ["Form", "Parents", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Parents", "Rows", "Items"], repeatability := some 2 },
    { level := 30, path := ["Form", "Parents", "Lookup"], repeatability := some 2 }] }

private def inputs (key : Option SemanticIndexKey := some (.text "a")) : MessageReferenceInputs := {
  cache := { insertions := [
    { group := 10, parentPath := [1], key := .text "a", row := 1 },
    { group := 10, parentPath := [1], key := .text "b", row := 3 },
    { group := 10, parentPath := [1], key := .text "b", row := 2 },
    { group := 10, parentPath := [2], key := .text "a", row := 2 }] }
  keyAt := fun address => if address.field == 1 && address.path == [1] then key
    else if address.field == 1 && address.path == [2] then some (.text "a") else none }

private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => if name == "Code" then some (fun _ _ => none) else none }

private def project (text : String) (environment : Env := [(1, 1)])
    (context : Option MessageReferenceInputs := some (inputs))
    (rowGroup : GroupPath := ["Form", "Parents"]) :
    Option (Except ReferenceProjectionError (List MessagePointer)) := do
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model rowGroup false parsed.body (world := world)).toOption
  pure (condition.core.referencePointers environment context)

private def hasPointers (text : String) (expected : List MessagePointer)
    (environment : Env := [(1, 1)])
    (context : Option MessageReferenceInputs := some (inputs))
    (rowGroup : GroupPath := ["Form", "Parents"]) : Bool :=
  match project text environment context rowGroup with
  | some (.ok actual) => actual.length == expected.length && expected.all actual.contains
  | _ => false

private def projectionError (text : String) (environment : Env)
    (context : Option MessageReferenceInputs)
    (rowGroup : GroupPath := ["Form", "Parents"]) : Option ReferenceProjectionError :=
  match project text environment context rowGroup with
  | some (.error error) => some error
  | _ => none

private def selected (fields : List FieldId) (parent : Nat := 1)
    (row : MessageRepetitionCoordinate := .concrete 1) (dynamic : Bool := true) :
    List MessagePointer :=
  (if dynamic then [{ field := 1, coordinates := [.concrete parent] }] else []) ++
    (3 :: fields).map fun field => { field, coordinates := [.concrete parent, row] }

example : hasPointers "[Rows/N For Key] > 0" (selected [4]) ∧
    hasPointers "[Rows/N For \"b\"] > 0" (selected [4] 1 (.concrete 2) false) ∧
    hasPointers "[Rows/N For Key] > 0" (selected [4] 2 (.concrete 2)) [(1, 2)] := by native_decide

example : hasPointers "Sum(Rows/Body For Key) > 0" (selected [8, 9]) ∧
    hasPointers "Sum(Rows/Items*/N For Key) > 0"
      (selected [] ++ [{ field := 10, coordinates := [.concrete 1, .concrete 1, .wildcard] }]) := by native_decide

example : [none, some (.text ""), some (.text "missing")].all (fun key =>
    hasPointers "[Rows/N For Key] > 0" (selected [4] 1 .unknown) [(1, 1)] (some (inputs key)) &&
    hasPointers "Sum(Rows/Items*/N For Key) > 0"
      (selected [] 1 .unknown ++ [{ field := 10, coordinates := [.concrete 1, .unknown, .wildcard] }])
      [(1, 1)] (some (inputs key))) = true := by native_decide

example : hasPointers "[Anchor] > 0 Or [Rows/N For Key] > 0"
    ({ field := 2, coordinates := [.concrete 1] } :: selected [4]) ∧
    hasPointers "[Rows/N For Key] > 0" (selected [4] 1 (.concrete 2)) [(1, 1)] (some (inputs (some (.text "b")))) := by native_decide

example : projectionError "[Rows/N For Key] > 0" [(1, 1)] none = some .missingIndexContext ∧
    projectionError "[Rows/N For Key] > 0" [] (some (inputs)) = some (.binding (.missingBinding 1)) := by native_decide

example : hasPointers "[Anchor] > 0" [{ field := 2, coordinates := [.concrete 1] }] [(1, 1)] none ∧
    hasPointers "Sum(Rows*/N) > 0" [{ field := 4, coordinates := [.concrete 1, .wildcard] }] [(1, 1)] none := by native_decide

example : ["Length(Rows/Text For Key) > 0", "[Rows/Text For Key] + \"!\" == \"x!\"",
    "[Rows/Text For Key] PatternMatched \"[0-9]+\"", "Valid(Rows/Text For Key,\"Code\")"].all
    (fun text => hasPointers text (selected [5])) = true := by native_decide

example : ["AtLeastOneFieldFilled(Rows/N For Key,Anchor)",
    "FirstFilledValue(Rows/N For Key,Anchor) > 0"].all
    (fun text => hasPointers text ({ field := 2, coordinates := [.concrete 1] } :: selected [4])) = true := by native_decide

example : hasPointers "NumberOfValueInFields(True In Rows/Flag For \"a\",Rows/Flag For \"b\") > 0"
    (selected [6] 1 (.concrete 1) false ++ selected [6] 1 (.concrete 2) false) ∧
    hasPointers "FirstFilledValue(Rows/Flag For Key,Fallback) == True"
      ({ field := 12, coordinates := [.concrete 1] } :: selected [6]) ∧
    hasPointers "FirstFilledValue(Rows/Text For Key,Key) == \"x\"" (selected [5]) := by native_decide

example : hasPointers "SumOfProducts(Rows/Items*/N For \"a\",Rows/Items*/M For \"b\") > 0"
    [{ field := 3, coordinates := [.concrete 1, .concrete 1] },
      { field := 10, coordinates := [.concrete 1, .concrete 1, .wildcard] },
      { field := 3, coordinates := [.concrete 1, .concrete 2] },
      { field := 11, coordinates := [.concrete 1, .concrete 2, .wildcard] }] := by native_decide

example : ["YearFromDate(AddDays(Rows/Stamp For Key,1)) > 2020",
    "AddDays(Rows/Stamp For Key,1) > Date(\"1\",\"1\",\"2024\")"].all
    (fun text => hasPointers text (selected [7])) = true := by native_decide

example : hasPointers "Invalid(Date(Rows/Day For Key,\"1\",YearFromDate(AddDays(Rows/Stamp For Key,1))))"
    (selected [13, 7]) := by native_decide

example : hasPointers "FieldFilled(Rows/N For Key)" (selected [4]) ∧
    hasPointers "GroupFilled(Rows/Body For Key)" (selected [8, 9]) ∧
    hasPointers "AtLeastOneGroupFilled(Rows/Body For \"a\",Rows/Body For \"b\")"
      (selected [8, 9] 1 (.concrete 1) false ++ selected [8, 9] 1 (.concrete 2) false) := by native_decide

example : ["NumberOfDifferentValues(Rows/Stamp For \"a\",Rows/Stamp For \"b\") > 0",
    "FieldValuesNotUnique(Rows/Stamp For \"a\",Rows/Stamp For \"b\")"].all
    (fun text => hasPointers text (selected [7] 1 (.concrete 1) false ++ selected [7] 1 (.concrete 2) false)) = true := by native_decide

example : hasPointers "MinValue(Rows/Items*/Stamp For Key) > Date(\"1\",\"1\",\"2024\")"
    (selected [] ++ [{ field := 14, coordinates := [.concrete 1, .concrete 1, .wildcard] }]) := by native_decide

example : projectionError "[/Form/Parents/Rows/N For LookupKey] > 0" [(1, 1)] (some (inputs))
    ["Form", "Parents", "Lookup"] = some (.binding (.missingBinding 30)) ∧
    hasPointers "[/Form/Parents/Rows/N For LookupKey] > 0"
      [{ field := 15, coordinates := [.concrete 1, .concrete 1] },
        { field := 3, coordinates := [.concrete 1, .concrete 2] },
        { field := 4, coordinates := [.concrete 1, .concrete 2] }]
      [(1, 1), (30, 1)]
      (some { inputs with keyAt := fun address =>
        if address.field == 15 && address.path == [1, 1] then some (.text "b") else none })
      ["Form", "Parents", "Lookup"] := by native_decide

example : projectionError "[Rows/N For Key] > 0" [(1, 1), (1, 2)] (some (inputs)) =
    some (.binding (.duplicateBinding 1)) ∧
    projectionError "[Rows/N For Key] > 0" [(1, 0)] (some (inputs)) =
      some (.binding (.zeroBinding 1)) := by native_decide

example : hasPointers "MinValue(Stamp,Stamp For \"a\") > Date(\"1\",\"1\",\"2024\")"
    [{ field := 7, coordinates := [.concrete 1, .concrete 3] },
      { field := 3, coordinates := [.concrete 1, .concrete 1] },
      { field := 7, coordinates := [.concrete 1, .concrete 1] }]
    [(1, 1), (10, 3)] (some (inputs)) ["Form", "Parents", "Rows"] := by native_decide

example : ["NumberOfValueInFields(1 In Rows/N For Key,Anchor) > 0",
    "AtLeastOneFieldValueIncludedInValueList(Rows/N For Key In Anchor)",
    "AtLeastOneFieldValueIncludedInValueList(Anchor In Rows/N For Key)"].all
    (fun text => hasPointers text ({ field := 2, coordinates := [.concrete 1] } :: selected [4])) = true := by native_decide

example : ["NumberOfValueInFields(\"x\" In Rows/Text For Key,Key) > 0",
    "NumberOfDifferentValues(Rows/Text For Key,Key) > 0",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Text For Key In Key)",
    "AtLeastOneFieldValueIncludedInValueList(Key In Rows/Text For Key)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Text For Key In \"x\")"].all
    (fun text => hasPointers text (selected [5])) = true := by native_decide

example : hasPointers "NumberOfFilledFields(Rows/Body For Key) > 0" (selected [8, 9]) ∧
    hasPointers "Sum(Rows/Body For Key) > 0" (selected [8, 9] 1 .unknown)
      [(1, 1)] (some (inputs none)) ∧
    hasPointers "FirstFilledValue(Rows/Stamp For \"a\",Rows/Stamp For \"b\") == Date(\"1\",\"1\",\"2024\")"
      (selected [7] 1 (.concrete 1) false ++ selected [7] 1 (.concrete 2) false) := by native_decide

example : ["N", "Text"].all (fun field =>
    hasPointers ("FieldValuesNotUnique(Rows/" ++ field ++ " For \"a\",Rows/" ++ field ++ " For \"b\")")
      (selected [if field == "N" then 4 else 5] 1 (.concrete 1) false ++
       selected [if field == "N" then 4 else 5] 1 (.concrete 2) false)) = true := by native_decide

end A12Kernel.Dm.SelectedMessageLocks
