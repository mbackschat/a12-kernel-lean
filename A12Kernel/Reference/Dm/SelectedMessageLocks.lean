import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Elaboration.ValidationCondition.Omission
import A12Kernel.Semantics.MessageIndex
import A12Kernel.Reference.Dm.Document

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
  cache := .known { insertions := [
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

private def omissionProject (text : String) (environment : Env := [(1, 1)])
    (context : Option MessageReferenceInputs := some (inputs)) :
    Option (List MessagePointer) := do
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form", "Parents"] false parsed.body (world := world)).toOption
  (condition.core.omissionPointers environment context).toOption

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

example : omissionProject "[Rows/N For Key] > 0" = some (selected [4]) ∧
    omissionProject "[Rows/N For Key] > 0" [(1, 2)] = some (selected [4] 2 (.concrete 2)) ∧
    omissionProject "FieldFilled(Rows/N For Key)" = some [] ∧
    omissionProject "FieldNotFilled(Rows/N For Key)" = some (selected [4]) ∧
    omissionProject "[Rows/N For Key] > 0" [(1, 1)] (some (inputs none)) =
      some (selected [4] 1 .unknown) := by native_decide

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

private def populationModel : FlatModel := {
  fields := (model.fields.filter fun field => [1, 3, 4].contains field.id) ++
    (List.range 20).map (fun index => {
      id := 100 + index, name := s!"F{index}", groupPath := ["Form"],
      policy := { kind := .number { scale := 0, signed := true } } })
  repeatableGroups := model.repeatableGroups.take 2 }

private def populationDocument (last : String) (indexName : String := "Id")
    (firstIndex : String := "b") (firstFiller : String := "F0")
    (rowGroup : String := "Rows") : Lean.Json :=
  let rows := [Lean.Json.mkObj [(indexName, .str firstIndex)], Lean.Json.mkObj [(indexName, .str "b")]]
  Lean.Json.mkObj [("Form", .mkObj (
    [("Parents", .arr #[.mkObj [("Key", .str "b"),
      (rowGroup, .arr rows.toArray)]])] ++
    (List.range 20).map (fun index => (if index == 0 then firstFiller else s!"F{index}",
      .str (if index == 19 then last else "1")))))]

private def populationPreliminary (last : String) (candidate : FlatModel := populationModel)
    (indexName : String := "Id") (firstIndex : String := "b") (firstFiller : String := "F0")
    (rowGroup : String := "Rows") :
    Option (CheckedIndexPreliminary candidate) := do
  let dm : DmModel := {
    flat := candidate, rules := [], computations := [],
    conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (populationDocument last indexName firstIndex firstFiller rowGroup)).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  checked.applyFullIndexPreliminary.toOption

private def derivedProjection (last : String) : Option (List MessagePointer) := do
  let preliminary ← populationPreliminary last
  let context ← preliminary.messageReferenceInputs.toOption
  let expression ← (parseText .english "[Rows/N For Key] > 0").toOption
  let condition ← (lowerCondition populationModel ["Form", "Parents"] false expression.body (world := world)).toOption
  (condition.core.referencePointers [(1, 1)] (some context)).toOption

example : derivedProjection "" = some (selected [4] 1 (.concrete 2)) ∧
    derivedProjection "1" = some (selected [4] 1 (.concrete 1)) ∧
    derivedProjection "bad" = derivedProjection "" := by native_decide

example : (populationPreliminary "1").map (fun preliminary =>
    (preliminary.base.messageKeyAt? { field := 3, path := [1, 1] },
      preliminary.messageQueryKeyAt? { field := 3, path := [1, 1] })) =
    some (some (.text "b"), none) := by native_decide

private def renamedPopulationModel : FlatModel := {
  populationModel with fields := populationModel.fields.map fun field =>
    if field.id == 3 then { field with name := "Key" } else field }

private def reservedPopulationModel : FlatModel := {
  renamedPopulationModel with fields := renamedPopulationModel.fields.map fun field =>
    if field.id == 100 then { field with name := "Key_0" } else field }

example : (renamedPopulationModel.messageFieldNames.filter fun entry => [1, 3, 100].contains entry.1) =
    [(100, "F0"), (1, "Key_0"), (3, "Key_1")] ∧
    (reservedPopulationModel.messageFieldNames.filter fun entry => [1, 3, 100].contains entry.1) =
      [(100, "Key_0"), (1, "Key_1"), (3, "Key_2")] := by native_decide

private def namedPopulationResult (candidate : FlatModel) (last : String) (indexName : String)
    (firstFiller : String := "F0") (firstIndex : String := "b") :
    Option (Nat × MessageRepetitionCoordinate × List MessagePointer) := do
  let preliminary ← populationPreliminary last candidate indexName firstIndex firstFiller
  let population ← preliminary.base.messageCachePopulation.toOption
  let context ← preliminary.messageReferenceInputs.toOption
  let expression ← (parseText .english "[Rows/N For Key] > 0").toOption
  let condition ← (lowerCondition candidate ["Form", "Parents"] false expression.body (world := world)).toOption
  let pointers ← (condition.core.referencePointers [(1, 1)] (some context)).toOption
  pure (population.length, ← (context.cache.lookup 10 [1] (some (.text "b"))).toOption, pointers)

example : ["", "1"].all (fun last =>
    (namedPopulationResult renamedPopulationModel last "Key").map (fun (_, row, pointers) => (row, pointers)) ==
      some (.concrete 1, selected [4] 1 (.concrete 1)) &&
    (namedPopulationResult reservedPopulationModel last "Key" "Key_0").map (fun (_, row, pointers) => (row, pointers)) ==
      some (.concrete 2, selected [4] 1 (.concrete 2))) = true := by native_decide

example : [(populationModel, "Id", "F0"), (renamedPopulationModel, "Key", "F0"),
    (reservedPopulationModel, "Key", "Key_0")].all (fun (candidate, indexName, firstFiller) =>
      (namedPopulationResult candidate "" indexName firstFiller "a").map (fun (_, row, pointers) => (row, pointers)) ==
        some (.concrete 2, selected [4] 1 (.concrete 2))) = true := by native_decide

private def collisionNames : List String :=
  ["CEFRZTCKM", "CHQRBUERC"].flatMap fun nameSeed =>
    (List.range 16).map fun index => nameSeed ++ String.join ((List.range 4).map fun bit =>
      if index / 2 ^ bit % 2 == 0 then "Aa" else "BB")

private def isolatedCacheModel : FlatModel := {
  fields := [
    { id := 1, name := "K6270", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 2, name := "StableKey", groupPath := ["Form", "Stable"], repeatableScope := [20], policy := { kind := .string } },
    { id := 3, name := "N", groupPath := ["Form", "Stable"], repeatableScope := [20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "StableKey", groupPath := ["Form", "Other"], repeatableScope := [30], policy := { kind := .string } },
    { id := 5, name := "N", groupPath := ["Form", "Other"], repeatableScope := [30], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 6, name := "Anchor", groupPath := ["Form"], policy := { kind := .string } }] ++
    collisionNames.zipIdx.map (fun (name, index) =>
      { id := 100 + index, name, groupPath := ["Form"], policy := { kind := .string } })
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 1 },
    { level := 20, path := ["Form", "Stable"], repeatability := some 2, indexField := some 2 },
    { level := 30, path := ["Form", "Other"], repeatability := some 2, indexField := some 4 }] }

private def isolatedCacheResults (first second : String) (partialCall : Bool) :
    Except String (List MessageRepetitionCoordinate × List (List MessageRepetitionCoordinate) × Bool) := do
  let dm : DmModel := { flat := isolatedCacheModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let stored := Lean.Json.mkObj [("Form", .mkObj (
    [("Anchor", .str "x"),
     ("Rows", .arr #[.mkObj [("K6270", .str "b")], .mkObj [("K6270", .str "b")]]),
     ("Stable", .arr #[.mkObj [("StableKey", .str first), ("N", .str "1")],
       .mkObj [("StableKey", .str second), ("N", .str "1")]]),
     ("Other", .arr #[.mkObj [("StableKey", .str "s"), ("N", .str "2")]])] ++
      collisionNames.map (fun name => (name, .str "x"))))]
  let input ← (readDocument dm stored).mapError reprStr
  if !input.refusals.isEmpty then throw (reprStr input.refusals)
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  let context ← if partialCall then do
    let view ← checked.applyPartialGeneratedPreliminary [RelevantEntityPattern.allInstances ["Form"]] |>.mapError reprStr
    view.messageReferenceInputs.mapError reprStr
    else do
      let view ← checked.applyFullIndexPreliminary.mapError reprStr
      view.messageReferenceInputs.mapError reprStr
  let expression ← (parseText .english "FieldFilled(Anchor) Or [Stable/N For \"s\"] > 0").mapError reprStr
  let condition ← (lowerCondition dm.flat ["Form"] false expression.body (world := world)).mapError reprStr
  let pointers ← (condition.core.referencePointers [] (some context)).mapError reprStr
  let some payload := pointers.find? (·.field == 3) | throw "missing stable payload"
  let ambiguousExpression ← (parseText .english "FieldFilled(Anchor) Or FieldFilled(Rows/K6270 For \"b\")").mapError reprStr
  let ambiguousCondition ← (lowerCondition dm.flat ["Form"] false ambiguousExpression.body (world := world)).mapError reprStr
  let refused := match ambiguousCondition.core.referencePointers [] (some context) with
    | .error (.hostOrder (.unresolvedBucket 10 [] (.text "b"))) => true
    | _ => false
  let rule : DmRule := {
    group := ["Form", "Stable"], name := "ParallelStable", errorCode := "ParallelStable",
    severity := "ERROR", errorEntityRelPath := "../N",
    condition := "FieldFilled(/Form/Stable/N) Or FieldFilled(/Form/Other/N)" }
  let plan ← (checkParallelRule dm .english rule).mapError reprStr
  let messages ← if partialCall then runPartialParallelRule checked plan [RelevantEntityPattern.allInstances ["Form"]]
    else runValidationRule world checked (.parallel plan)
  pure (payload.coordinates, messages.map (·.errorAddress.coordinates), refused)

-- The query-isolation capture preserves a host-sensitive collision beside these stable lookups (docs/sources/message-cache-probes.md#src-message-cache-query-isolation).
#guard [false, true].all fun partialCall =>
  (isolatedCacheResults "t" "s" partialCall).toOption ==
    some ([.concrete 2], [[.concrete 2], [.concrete 1]], true) &&
  (isolatedCacheResults "s" "s" partialCall).toOption ==
    some ([.concrete 1], [[.concrete 1]], true) &&
  (isolatedCacheResults "t" "u" partialCall).toOption ==
    some ([.unknown], [[.unknown], [.concrete 1], [.concrete 2]], true)

private def namedGroupPopulation (rowGroup otherGroup : String) : FlatModel := {
  populationModel with
    fields := (populationModel.fields.map fun field =>
      if field.groupPath == ["Form", "Parents", "Rows"] then
        { field with groupPath := ["Form", "Parents", rowGroup] } else field) ++
      [{ id := 200, name := "Id", groupPath := ["Form", "Parents", otherGroup],
         repeatableScope := [1], policy := { kind := .string } }]
    repeatableGroups := populationModel.repeatableGroups.map fun group =>
      if group.level == 10 then { group with path := ["Form", "Parents", rowGroup] } else group }

private def namedGroupProjection (rowGroup otherGroup last : String) (partialCall : Bool)
    (firstIndex : String := "b") : Option (List MessagePointer) := do
  let candidate := namedGroupPopulation rowGroup otherGroup
  let preliminary ← populationPreliminary last candidate "Id" firstIndex "F0" rowGroup
  let context ← if partialCall then do
    let view ← (preliminary.base.applyPartialGeneratedPreliminary
      [RelevantEntityPattern.allInstances ["Form"]]).toOption
    view.messageReferenceInputs.toOption
    else preliminary.messageReferenceInputs.toOption
  let expression ← (parseText .english ("[" ++ rowGroup ++ "/N For Key] > 0")).toOption
  let condition ← (lowerCondition candidate ["Form", "Parents"] false expression.body
    (world := world)).toOption
  (condition.core.referencePointers [(1, 1)] (some context)).toOption

-- The legal-name cache checkpoint distinguishes UTF-16 lexical order from declaration or locale order (docs/sources/message-cache-probes.md#src-message-cache-legal-names).
example : [false, true].all (fun partialCall =>
    namedGroupProjection "Gä" "Gz" "" partialCall == some (selected [4] 1 (.concrete 2)) &&
    namedGroupProjection "Gä" "Gz" "1" partialCall == some (selected [4] 1 (.concrete 2)) &&
    namedGroupProjection "Gz" "Gä" "" partialCall == some (selected [4] 1 (.concrete 2)) &&
    namedGroupProjection "Gz" "Gä" "1" partialCall == some (selected [4] 1 (.concrete 1)) &&
    namedGroupProjection "Gä" "Gz" "1" partialCall "a" == some (selected [4] 1 (.concrete 2)) &&
    namedGroupProjection "Gz" "Gä" "1" partialCall "a" == some (selected [4] 1 (.concrete 2))) = true := by native_decide

private def populationPartial (entities : List RelevantEntityPattern) :
    Option (CheckedPartialPreliminary populationModel) := do
  let full ← populationPreliminary "1"
  (full.base.applyPartialGeneratedPreliminary entities).toOption

private def partialProjection (entities : List RelevantEntityPattern) : Option (List MessagePointer) := do
  let view ← populationPartial entities
  let context ← view.messageReferenceInputs.toOption
  let expression ← (parseText .english "[Rows/N For Key] > 0").toOption
  let condition ← (lowerCondition populationModel ["Form", "Parents"] false expression.body (world := world)).toOption
  (condition.core.referencePointers [(1, 1)] (some context)).toOption

private def withoutLastFiller : List RelevantEntityPattern :=
  RelevantEntityPattern.allInstances ["Form", "Parents"] ::
    (List.range 19).map fun index => RelevantEntityPattern.allInstances ["Form", s!"F{index}"]

example : partialProjection [RelevantEntityPattern.allInstances ["Form"]] =
    some (selected [4] 1 (.concrete 1)) := by native_decide

example : partialProjection withoutLastFiller =
    some (selected [4] 1 (.concrete 2)) := by native_decide

private def relevantIndexRow (row : Nat) : RelevantEntityPattern := {
  path := ["Form", "Parents", "Rows", "Id"]
  indices := [.all, .concrete 1, .concrete row, .all] }

private def partialPopulationSummary (entities : List RelevantEntityPattern) :
    Option (Nat × Nat × Nat × Option SemanticIndexKey) := do
  let view ← populationPartial entities
  let population ← view.messageCachePopulation.toOption
  let cache ← view.deriveMessageCache.toOption
  pure (population.length, (population.filterMap (·.association)).length,
    cache.insertions.length, view.messageQueryKeyAt? { field := 1, path := [1] })

example : [1, 2].all (fun row =>
    partialProjection [RelevantEntityPattern.allInstances ["Form", "Parents", "Key"], relevantIndexRow row] ==
      some (selected [4] 1 (.concrete row)) &&
    partialPopulationSummary [RelevantEntityPattern.allInstances ["Form", "Parents", "Key"], relevantIndexRow row] ==
      some (4, 1, 1, some (.text "b"))) = true := by native_decide

example : [1, 2].all (fun row =>
    partialProjection [relevantIndexRow row] == some (selected [4] 1 .unknown) &&
    partialPopulationSummary [relevantIndexRow row] == some (3, 1, 1, none)) = true := by native_decide

example : partialPopulationSummary [] = some (0, 0, 0, none) ∧
    partialProjection [] = some (selected [4] 1 .unknown) := by native_decide

example : (populationPartial [RelevantEntityPattern.allInstances ["Form"]]).map (fun view =>
    (view.index.base.messageKeyAt? { field := 3, path := [1, 1] },
      view.messageQueryKeyAt? { field := 3, path := [1, 1] })) =
    some (some (.text "b"), none) := by native_decide

private def listBinModel : FlatModel := {
  fields := [
    { id := 1, name := "K6270", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 2, name := "Anchor", groupPath := ["Form"], policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 1 }] }

private def listBinProjection : Option (List MessagePointer) := do
  let dm : DmModel := { flat := listBinModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", .mkObj [
    ("Anchor", .str "x"), ("Rows", .arr #[.mkObj [("K6270", .str "b")], .mkObj [("K6270", .str "b")]])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler listBinModel).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let preliminary ← checked.applyFullIndexPreliminary.toOption
  let context ← preliminary.messageReferenceInputs.toOption
  let expression ← (parseText .english "FieldFilled(Anchor) Or FieldFilled(Rows/K6270 For \"b\")").toOption
  let condition ← (lowerCondition listBinModel ["Form"] false expression.body (world := world)).toOption
  (condition.core.referencePointers [] (some context)).toOption

example : listBinProjection = some [
    { field := 2, coordinates := [] }, { field := 1, coordinates := [.concrete 1] }] := by native_decide

private def implicitParentDocument : Option (CheckedDocument model) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let json := Lean.Json.mkObj [("Form", .mkObj [("Parents", .arr #[.mkObj [
    ("Key", .str "a"), ("Anchor", .str "1"), ("Rows", .arr #[.mkObj [
      ("Id", .str "a"), ("N", .str "2"), ("Text", .str "x"),
      ("Flag", .str "true"), ("Stamp", .str "2024-01-01")]])]])])]
  let raw ← (readDocument dm json).toOption
  if !raw.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def implicitParentVerdicts (condition : String) : Option (List Verdict) := do
  let document ← implicitParentDocument
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let rule ← (checkRule dm .english {
    name := "ImplicitKey", group := ["Form", "Parents"], errorEntityRelPath := "../Anchor",
    errorCode := "PROBE", condition, severity := "ERROR" } world).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  pure (outcomes.map fun (_, outcome) => outcome.verdict)

example : implicitParentDocument.isSome ∧
    implicitParentVerdicts "FieldFilled(Anchor)" = some [.fired .value, .notFired] := by native_decide

example : implicitParentVerdicts "FieldFilled(Anchor) Or [Rows/N For Key] > 0" =
    some [.fired .value, .notFired] := by native_decide

example : ["N", "Text", "Flag", "Stamp"].all (fun field =>
    implicitParentVerdicts ("FieldFilled(Anchor) And FieldFilled(Rows/" ++ field ++ " For Key)") ==
      some [.fired .value, .notFired]) = true := by native_decide

example : implicitParentVerdicts "FieldFilled(Anchor) Or [Rows/N For Key] == 0" =
      some [.fired .value, .fired .omission] ∧
    implicitParentVerdicts "[Rows/N For Key] == 0 Or FieldFilled(Anchor)" =
      some [.fired .value, .fired .omission] := by native_decide

private def implicitParentIndexedSource (field : String := "N") : Option (CheckedSemanticIndexSource model) := do
  let parsed ← (parseText .english ("FieldFilled(Rows/" ++ field ++ " For Key)")).toOption
  let condition ← (lowerCondition model ["Form", "Parents"] false parsed.body (world := world)).toOption
  match condition.core with
  | .leaf (.indexedFieldPresence .filled source) => some source
  | _ => none

private def implicitParentObservation (environment : Env) (phase : Phase) : Option CellObservation := do
  let document ← implicitParentDocument
  let source ← implicitParentIndexedSource "N"
  (source.observeDocument document environment phase).toOption

private def implicitParentSourceError (environment : Env) (phase : Phase)
    (expected : CheckedAddressingError) : Bool :=
  match implicitParentDocument, implicitParentIndexedSource "N" with
  | some document, some source =>
      match source.observeDocument document environment phase with
      | .error actual => actual == expected
      | .ok _ => false
  | _, _ => false

example : (implicitParentIndexedSource "N").isSome := by native_decide

example : implicitParentObservation [(1, 1)] .validation = some (.value (.num 2)) ∧
    implicitParentObservation [(1, 1)] .computation = some (.value (.num 2)) := by native_decide

example : implicitParentObservation [(1, 2)] .validation = some .empty ∧
    implicitParentSourceError [(1, 2)] .computation
      (.document (.missingRow { group := 1, path := [2] })) ∧
    implicitParentSourceError [(1, 3)] .validation
      (.document (.missingRow { group := 1, path := [3] })) := by native_decide

example : [Phase.validation, .computation].all (fun phase =>
    implicitParentSourceError [] phase
      (.semanticIndex (.checkedColumn (.environment (.missingBinding 1)))) &&
    implicitParentSourceError [(1, 0)] phase
      (.semanticIndex (.checkedColumn (.environment (.zeroBinding 1)))) &&
    implicitParentSourceError [(1, 1), (1, 2)] phase
      (.semanticIndex (.checkedColumn (.environment (.duplicateBinding 1))))) = true := by native_decide

private def typedImplicitKeyControl (field : String) : Bool :=
  match implicitParentDocument, implicitParentIndexedSource field with
  | some document, some source =>
      let physical := match source.observeDocument document [(1, 1)] .validation with
        | .ok (.value _) => true
        | _ => false
      physical && (source.observeDocument document [(1, 2)] .validation).toOption == some .empty
  | _, _ => false

example : ["N", "Text", "Flag", "Stamp"].all typedImplicitKeyControl = true := by native_decide

end A12Kernel.Dm.SelectedMessageLocks
