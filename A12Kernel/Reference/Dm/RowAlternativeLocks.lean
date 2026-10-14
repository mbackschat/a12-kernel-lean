import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! # Repeatable alternative selection and dependencies

Internal composition locks for spec/09's first-selection, poison and static dependency distinctions.
The population replay separately calibrates the retained String guard and Enumeration literal rows.
-/

namespace A12Kernel.Dm.RowAlternativeLocks

open A12Kernel A12Kernel.Dm Lean

private def field (id : FieldId) (name : String) (kind : FieldKind) : FlatFieldDecl := {
  id, name, groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind } }
private def domain : EnumerationDeclaration := { storedTokens := ["A", "B"] }
private def model : FlatModel := {
  fields := [field 1 "Gate" (.number { scale := 0, signed := true }),
    { field 2 "Text" .string with stringPolicy := { maxLength := some 3 } },
    { field 3 "Enum" .enumeration with enumeration := some domain },
    { field 4 "Source" .enumeration with enumeration := some domain },
    { id := 5, name := "Out", groupPath := ["Form"],
      policy := { kind := .number { scale := 0, signed := true } } },
    { field 6 "Left" .string with groupPath := ["Form", "Rows", "Box"] },
    { field 7 "Right" .string with groupPath := ["Form", "Rows", "Box"] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def definition (target : String) (alternatives : List DmAlternative)
    (common : Option String := none) : DmComputation := {
  group := ["Form", "Rows"], name := target, targetRelPath := "../" ++ target
  commonPrecondition := common, alternatives, errorCodesToSuppress := [] }

private def run (definitions : List DmComputation) (gates : List String) (source : String := "A") :
    Option (List (String × String)) := do
  let dm : DmModel := {
    flat := model, rules := [], computations := definitions
    conditionLanguage := "en_US", refusals := [] }
  let rows := gates.map fun gate => Json.mkObj [
    ("Gate", Json.str gate), ("Text", "old"), ("Enum", "B"), ("Source", Json.str source),
    ("Box", Json.mkObj [("Left", "old"), ("Right", "old")])]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Rows", Json.arr rows.toArray), ("Out", "9")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map fun value =>
    (value.pointer, value.outcome))

private def guarded (text guard : String) : DmAlternative := { operation := text, precondition := some guard }

example : run [definition "Text" [guarded "\"A\"" "CurrentRepetition(/Form/Rows) == 1",
    guarded "\"B\"" "CurrentRepetition(/Form/Rows) == 2"]] ["", "", "bad"] =
    some [("Form/Rows/Text", "value A"), ("Form/Rows[2]/Text", "value B"),
      ("Form/Rows[3]/Text", "cleared")] := by native_decide

example : run [definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"]]
    ["", "bad"] = some [("Form/Rows/Text", "cleared"), ("Form/Rows[2]/Text", "cleared")] ∧
    run [definition "Text" [guarded "\"LONG\"" "FieldFilled(Gate)",
      guarded "\"B\"" "FieldFilled(Gate)"]] ["1"] =
      some [("Form/Rows/Text", "errored LONG")] ∧
    run [definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"] (some "FieldNotFilled(Gate)")]
      ["1"] = some [("Form/Rows/Text", "cleared")] ∧
    run [definition "Text" [guarded "\"LONG\"" "FieldFilled(Gate)"]] [] = some [] := by native_decide

example : run [definition "Enum" [{ operation := "\"A\"", precondition := none }]] ["", "", ""] =
    some [("Form/Rows/Enum", "value A"), ("Form/Rows[2]/Enum", "value A"),
      ("Form/Rows[3]/Enum", "cleared")] ∧
    run [definition "Enum" [guarded "[Source]" "FieldFilled(Gate)",
      guarded "\"A\"" "FieldNotFilled(Gate)"]] ["1", ""] =
      some [("Form/Rows/Enum", "value A"), ("Form/Rows[2]/Enum", "value A")] := by native_decide

example : [definition "Text" [{ operation := "\"A\"", precondition := none }, guarded "\"B\"" "FieldFilled(Gate)"]
      (some "FieldFilled(Gate)"),
    definition "Text" [guarded "\"A\"" "FieldFilled(Text)"],
    definition "Enum" [{ operation := "\"OUTSIDE\"", precondition := none }],
    definition "Enum" [{ operation := "[Enum]", precondition := none }]].all
      (fun value => !(lowerComputation model .english value).isOk) := by native_decide

private def count : DmComputation := {
  group := ["Form"], name := "Count", targetRelPath := "../Out", commonPrecondition := none
  alternatives := [{ operation := "NumberOfDifferentValues(Rows*/Text)", precondition := none }]
  errorCodesToSuppress := [] }

example : run [count, definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"]] [""] =
    some [("Form/Rows/Text", "cleared"), ("Form/Out", "value 0")] ∧
    run [count, definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"]] ["bad"] =
    some [("Form/Rows/Text", "cleared"), ("Form/Out", "cleared")] := by native_decide

example : run [definition "Text" [guarded "\"\"" "FieldFilled(Gate)",
    guarded "\"B\"" "FieldFilled(Gate)"]] ["1"] = some [("Form/Rows/Text", "cleared")] ∧
    run [definition "Enum" [guarded "\"A\"" "FieldNotFilled(Gate)",
      guarded "[Source]" "FieldFilled(Gate)"]] [""] "bad" =
      some [("Form/Rows/Enum", "value A")] := by native_decide

example : run [definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"],
    definition "Gate" [{ operation := "1", precondition := none }]] [""] =
    some [("Form/Rows/Gate", "value 1"), ("Form/Rows/Text", "value A")] ∧
    run [definition "Text" [guarded "\"A\"" "GroupFilled(/Form/Rows)"],
      definition "Gate" [guarded "1" "GroupFilled(/Form/Rows)"]] [""] =
    some [("Form/Rows/Text", "value A"), ("Form/Rows/Gate", "value 1")] := by native_decide

private def boxDefinition (target value : String) : DmComputation :=
  { definition target [guarded value "GroupFilled(/Form/Rows/Box)"] with
    group := ["Form", "Rows", "Box"] }

example : run [boxDefinition "Left" "\"A\"", boxDefinition "Right" "\"B\""] [""] =
    some [("Form/Rows/Box/Left", "cleared"), ("Form/Rows/Box/Right", "cleared")] := by native_decide

private def planHasCycle (definitions : List DmComputation) : Option Bool := do
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption.map (·.2)
  let steps := lowered.map (·.toMixedStep builtinStringPatternCompiler)
  match certifyAuthoredMixedComputationPlan steps with
  | .error (.cycle _ _) => some true
  | .ok _ => some false
  | .error _ => none

private def unreachableCopy : DmComputation := definition "Enum"
  [guarded "\"A\"" "CurrentRepetition(/Form/Rows) >= 1", guarded "[Source]" "FieldFilled(Gate)"]

example : planHasCycle [unreachableCopy, definition "Source" [{ operation := "[Enum]", precondition := none }]] =
    some true ∧
    planHasCycle [unreachableCopy, definition "Source" [{ operation := "\"A\"", precondition := none }]] =
    some false := by native_decide

private def plainBoxRight : DmComputation := {
  boxDefinition "Right" "\"B\"" with alternatives := [{ operation := "\"B\"", precondition := none }] }

example : planHasCycle [boxDefinition "Left" "\"A\"", boxDefinition "Right" "[Left]"] = some false ∧
    planHasCycle [boxDefinition "Left" "\"A\"", boxDefinition "Right" "[Left]", plainBoxRight] =
      some true := by native_decide

private def splitUnreachableCopy : List DmComputation :=
  unreachableCopy.alternatives.map fun alternative =>
    { unreachableCopy with alternatives := [alternative] }

example : planHasCycle (splitUnreachableCopy ++ [definition "Source" [{ operation := "[Enum]", precondition := none }]]) = some true ∧
    planHasCycle (splitUnreachableCopy ++ [definition "Source" [{ operation := "\"A\"", precondition := none }]]) = some false := by native_decide

example : run [count, definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"],
    definition "Text" [{ operation := "\"B\"", precondition := none }]] [""] =
    some [("Form/Rows/Text", "value B"), ("Form/Out", "value 1")] ∧
    run [count, definition "Text" [guarded "\"A\"" "FieldFilled(Gate)"],
      definition "Text" [{ operation := "\"B\"", precondition := none }]] ["bad"] =
    some [("Form/Rows/Text", "cleared"), ("Form/Out", "cleared")] := by native_decide

private def fixedBooleanAlternatives (gate : String) (confirm : Bool := false)
    (first : String := "False") (common : Option String := none) (fresh : Bool := false)
    (firstGuard : Option String := some "[Gate] == 1") :
    Option (String × String) := do
  let number : FieldKind := .number { scale := 0, signed := true }
  let model : FlatModel := { fields := [
    { id := 1, name := "Gate", groupPath := ["Form"], policy := { kind := number } },
    { id := 2, name := "Out", groupPath := ["Form", "Box"],
      policy := { kind := if confirm then .confirm else .boolean } },
    { id := 3, name := "After", groupPath := ["Form", "Box"], policy := { kind := number } },
    { id := 4, name := "A", groupPath := ["Form"], policy := { kind := .boolean } },
    { id := 5, name := "B", groupPath := ["Form"], policy := { kind := .boolean } }] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", .mkObj [
    ("Gate", .str gate), ("A", .str "false"), ("B", .str "false"), ("Box", .mkObj [("Out", .str "bad"), ("After", .str "99")])])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let operation : DmComputation := {
    group := ["Form"], name := "Select", targetRelPath := "../Box/Out", commonPrecondition := common
    alternatives := [{ operation := first, precondition := firstGuard }, guarded "True" "[Gate] >= 0"], errorCodesToSuppress := [] }
  let dependent : DmComputation := {
    group := ["Form"], name := "After", targetRelPath := "../Box/After"
    commonPrecondition := some "FieldFilled(Box/Out) Or FieldNotFilled(Box/Out)"
    alternatives := [{ operation := "1", precondition := none }], errorCodesToSuppress := [] }
  let producer : DmComputation := {
    group := ["Form"], name := "FreshGate", targetRelPath := "../Gate", commonPrecondition := none
    alternatives := [{ operation := "1", precondition := none }], errorCodesToSuppress := [] }
  let steps ← ([dependent, operation] ++ if fresh then [producer] else []).mapM fun definition =>
    (lowerComputation model .english definition).toOption.map (·.2)
  let results ← (runComputations world prepared checked steps).toOption
  let outcome (name : String) := ((results.find? (·.pointer.endsWith name)).map (·.outcome)).getD "unchanged"
  pure (outcome "/Out", outcome "/After")

example : fixedBooleanAlternatives "1" = some ("value false", "value 1") ∧
    fixedBooleanAlternatives "2" = some ("value true", "value 1") ∧
    fixedBooleanAlternatives "-1" = some ("cleared", "value 1") ∧
    fixedBooleanAlternatives "" = some ("value true", "value 1") ∧
    fixedBooleanAlternatives "bad" = some ("cleared", "cleared") := by native_decide

example : fixedBooleanAlternatives "1" true "True" = some ("value true", "value 1") ∧
    fixedBooleanAlternatives "2" true "False" = none ∧
    fixedBooleanAlternatives "1" false "False" (some "[Gate] == 0") = some ("cleared", "value 1") ∧
    fixedBooleanAlternatives "bad" false "False" (some "[Gate] == 0") = some ("cleared", "cleared") := by
  native_decide

example : fixedBooleanAlternatives "-1" false "False" none true = some ("value false", "value 1") ∧
    fixedBooleanAlternatives "1" false "False" (some "[A] == [B]") = some ("value false", "value 1") ∧
    fixedBooleanAlternatives "1" false "False" (some "FieldFilled(Box/Out)") = none ∧
    fixedBooleanAlternatives "1" false "False" (some "FieldFilled(Gate)") false none = none := by
  native_decide

end A12Kernel.Dm.RowAlternativeLocks
