import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.StringExpressionLocks

private def enumDecl (name : String) (id : FieldId) (display : Bool := false) : FlatFieldDecl := {
  id, groupPath := ["Form"], name, policy := { kind := .enumeration }
  enumeration := some {
    storedTokens := ["a", "b"]
    displayFacts := if display then [
      { locale := "en", stored := "a", display := "Alpha" },
      { locale := "en", stored := "b", display := "Beta" }] else []
    categories := [{ name := "Kind", tokens := ["group", "other"] },
      { name := "Both", tokens := ["same", "same"] }] } }

private def model : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "S", policy := { kind := .string } },
    { id := 1, groupPath := ["Form"], name := "T", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 2, signed := true } } }, enumDecl "E" 4, enumDecl "L" 5 true ] }

private def admitted (source : String) (inputModel : FlatModel := model) : Bool :=
  match parseText .english source with
  | .ok parsed => (lowerCondition inputModel ["Form"] false parsed.body).isOk
  | .error _ => false

example : ["[S] + \"x\" == [T]", "RangeAsString(S,1,2) != \"x\"",
    "FieldValueAsString(N) + [S] == [T]"].all (fun source => admitted source) := by native_decide

private def checkedStored (text : String) : Option CheckedCell := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en" { instantiatedRows := [], cells := [
    { address := { field := 0, path := [] }, stored := text, raw := .parsed (.str text) }] }).toOption
  (← (checked.read { field := 0, path := [] }).toOption)

example : (checkedStored "😀b").map (·.findings) = some [.unsupportedCharacter] := by native_decide
example : (checkedStored "𝄞x").map (·.findings) = some [.unsupportedCharacter] := by native_decide

open Lean

private def execute (operation : String) (s n : String) (repeated : Bool := false)
    (condition : Option String := none) (custom : Bool := false) : Option (List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let model : FlatModel := { model with
    fields := model.fields.map (fun f => { f with
      groupPath := group, repeatableScope := scope
      customType := if custom && f.id == 0 then some { name := "Code" } else none }) ++
      [{
        id := 3, groupPath := group, name := "Out", repeatableScope := scope, policy := { kind := .string }
        customType := if custom then some { name := "Code", minLength := some 100 } else none }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("S", toJson s), ("T", "x"), ("E", "a"), ("L", "b"), ("N", toJson n), ("Out", "old")]
  let input := Json.mkObj [("Form", if repeated then Json.mkObj [("Rows", Json.arr #[row, row])] else row)]
  let data ← (readDocument dm input).toOption
  if !data.refusals.isEmpty then none
  let world : World := {
    now := { epochMillis := 0 }
    customFieldValidator? := fun name => if name == "Code" then
      some (fun value _ => if value == "ab" then none else some { projectCode := "BAD" }) else none }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let computation : DmComputation := {
    group, name := "Compute", targetRelPath := "../Out"
    commonPrecondition := condition, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let (_, step) ← (lowerComputation model .english computation).toOption
  pure ((← (runComputations world prepared checked [step]).toOption).map (·.outcome))

example : [false, true].all (fun repeated =>
    let expected value := some (List.replicate (if repeated then 2 else 1) value)
    execute "[S] + FieldValueAsString(N)" "ab" "01.50" repeated == expected "value ab1.5" &&
    execute "RangeAsString(S,1,6) + \"x\"" "ab" "1.50" repeated == expected "value x" &&
    execute "[S] + \"x\"" "" "1.50" repeated == expected "value x" &&
    execute "[S] + \"x\"" "😀b" "1.50" repeated == expected "cleared" &&
    execute "\"😀b\"" "ab" "1.50" repeated == expected "value 😀b" &&
    execute "\"yes\"" "ab" "1.50" repeated (some "[S] + \"x\" == \"abx\"") == expected "value yes" &&
    execute "\"yes\"" "ab" "1.50" repeated (some "[S] + \"x\" != \"\"") == expected "cleared") := by native_decide

private def messages (condition : String) (repeated : Bool := false) : Option Nat := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let model : FlatModel := { model with
    fields := model.fields.map fun f => { f with groupPath := group, repeatableScope := if repeated then [10] else [] }
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("S", "ab"), ("T", "x"), ("E", "a"), ("L", "b"), ("N", "1.50")]
  let input ← (readDocument dm (Json.mkObj [("Form", if repeated then Json.mkObj [("Rows", Json.arr #[row, row])] else row)])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group, name := "Rule", errorEntityRelPath := "../S",
    errorCode := "STR", condition, severity := "ERROR" }).toOption
  pure (← (runRule world checked rule).toOption).length

example : messages "RangeAsString(S,1,2) + FieldValueAsString(N) == \"ab1.5\"" true = some 2 := by native_decide
example : messages "[S] + \"x\" != \"\"" true = some 0 := by native_decide

example : messages "RangeAsString(S,1,2) + FieldValueAsString(N) == \"ab1.5\"" = some 1 := by native_decide
example : messages "[S] + \"x\" != \"\"" = some 0 := by native_decide

example : admitted "[E] + \"x\" == \"ax\"" = true := by native_decide
example : admitted "[L] + \"x\" == \"bx\"" = false := by native_decide
example : admitted "RangeAsString(E,1,1) + \"x\" == \"ax\"" = false := by native_decide
example : admitted "[L->Kind] + \"x\" == \"otherx\"" = true := by native_decide
example : [false, true].all (fun repeated =>
    execute "[E] + [L->Kind]" "ab" "1" repeated ==
      some (List.replicate (if repeated then 2 else 1) "value aother")) := by native_decide
example : messages "[S] + [L->Kind] + [E] == \"abothera\"" true = some 2 := by native_decide

private def partialVerdicts (condition : String) (repeated : Bool)
    (scope : ValidationRelevanceScope) : Option (List Verdict) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let model : FlatModel := { model with
    fields := model.fields.map fun f => { f with groupPath := group, repeatableScope := if repeated then [10] else [] }
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("S", "ab"), ("E", "a"), ("L", "b"), ("N", "01.50")]
  let input ← (readDocument dm (Json.mkObj [("Form", if repeated then Json.mkObj [("Rows", Json.arr #[row, row])] else row)])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group, name := "Rule", errorEntityRelPath := "../S",
    errorCode := "STR", condition, severity := "ERROR" }).toOption
  if repeated then
    match ← (rule.evalOrdinaryRepeatablePartial checked scope (some world)).toOption with
    | .skipped => none
    | .evaluated rows => rows.mapM fun (_, outcome) => match outcome with
        | .skipped => none
        | .evaluated result => some result.verdict
  else
    match ← (rule.evalAddressedPartial checked scope (some world)).toOption with
    | .skipped => none
    | .evaluated result => some [result.verdict]

example : [false, true].all (fun repeated =>
    partialVerdicts "[S] + [L->Kind] + FieldValueAsString(N) == \"abother1.5\"" repeated .full ==
      some (List.replicate (if repeated then 2 else 1) (.fired .value))) := by native_decide
example : partialVerdicts "[S] + [E] == \"aba\"" false
    (.partialSet [{ path := ["Form", "S"], indices := [.all, .all] }]) = some [.unknown] := by native_decide
example : partialVerdicts "[S] + [E] == \"aba\"" true
    (.partialSet [{ path := ["Form", "Rows", "S"], indices := [.all, .all, .all] }]) =
    some [.unknown, .unknown] := by native_decide

example : [false, true].all (fun repeated =>
    execute "[S] + \"x\"" "ab" "1" repeated none true ==
      some (List.replicate (if repeated then 2 else 1) "value abx") &&
    execute "[S] + \"x\"" "bad" "1" repeated none true ==
      some (List.replicate (if repeated then 2 else 1) "cleared") &&
    execute "\"a\n\" + \"b\"" "ab" "1" repeated none true ==
      some (List.replicate (if repeated then 2 else 1) "value a\nb")) := by native_decide

example : admitted "[L->Kind] == \"other\"" = true ∧
    admitted "[L->Kind] == \"outside\"" = false := by native_decide
example : admitted "[L->Missing] + \"x\" == \"ax\"" = false ∧
    admitted "[S->Kind] + \"x\" == \"ax\"" = false := by native_decide
example : admitted "[L] + \"x\" == \"bx\"" { model with
    fields := model.fields.map fun field => { field with enumeration := field.enumeration.map fun decl =>
      { decl with displayFacts := decl.displayFacts.map fun fact => { fact with display := fact.stored } } } } := by native_decide
example : execute "[E->Both] + [L->Both]" "ab" "1" = some ["value samesame"] := by native_decide
example : execute "\"x\" + [L->Kind]" "ab" "1" false
    (some "[E] + [L->Kind] == \"aother\"") = some ["value xother"] := by native_decide

end A12Kernel.Dm.StringExpressionLocks
