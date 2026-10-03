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
  let steps : List (MixedComputationStep model builtinStringPatternCompiler) := lowered.map fun
    | .number table _ => .number table
    | .parallel step => .parallel step
    | .string table => .string table
    | .document step => .document step
    | .rows step => .rows (step builtinStringPatternCompiler)
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

end A12Kernel.Dm.RowAlternativeLocks
