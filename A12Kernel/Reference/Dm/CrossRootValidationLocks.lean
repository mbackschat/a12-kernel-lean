import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # Cross-root full-validation admission and content gates

The retained rule-bucket grid owns the two-root Number result. Additional fixed-child, typed-atom,
connective and structural-coordinate cases are internal composition separators for spec/03 A.4.
-/

namespace A12Kernel.Dm.CrossRootValidationLocks
open A12Kernel A12Kernel.Dm Lean

private def number (id : FieldId) (group : GroupPath) (name : String) : FlatFieldDecl := {
  id, name, groupPath := group, policy := { kind := .number { scale := 0, signed := true } } }
private def model : FlatModel := {
  fields := [number 1 ["Form"] "N", number 2 ["Form", "Sub"] "A", number 3 ["Other"] "N",
    { id := 4, name := "Text", groupPath := ["Other"], policy := { kind := .string } },
    { id := 5, name := "Stamp", groupPath := ["Other"]
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { number 6 ["Other", "Rows"] "N" with repeatableScope := [10] },
    { id := 7, name := "Marker", groupPath := ["Form"], policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Other", "Rows"], repeatability := some 2 }] }
private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def rule (text : String) : DmRule := {
  group := ["Form"], name := "Rule", errorCode := "R", errorEntityRelPath := "../N"
  condition := text, severity := "ERROR" }
private def object (values : List (String × String)) : Json :=
  Json.mkObj (values.map fun (name, text) => (name, Json.str text))
private def run (text : String) (form other : List (String × String) := []) :
    Option (List (String × String)) := do
  let checkedRule ← (checkRule dm .english (rule text)).toOption
  let data := Json.mkObj [("Form", object form), ("Other", object other)]
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world document checkedRule).toOption).map fun message =>
    let observed := observe model message
    (observed.pointer, observed.messageType))

example : run "[/Other/N] + [N] < 5" = some [("Form/N", "OMISSION_ERROR")] ∧
    run "[/Other/N] + [N] < 5" [] [("N", "1")] = some [("Form/N", "OMISSION_ERROR")] ∧
    run "[/Other/N] + [N] < 5" [("N", "1")] [("N", "1")] = some [("Form/N", "VALUE_ERROR")] ∧
    run "[/Other/N] + [N] < 5" [] [("N", "bad")] = some [] ∧
    run "[/Other/N] + [N] < 5" [] [("N", "9")] = some [] := by native_decide

example : run "[Sub/A] + [N] < 5" = some [] ∧
    run "[Sub/A] + [N] < 5" [] [("Text", "foreign content")] = some [] ∧
    run "[Sub/A] + [N] < 5" [("Marker", "own content")] = some [("Form/N", "OMISSION_ERROR")] := by native_decide

example : run "Length(/Other/Text) + [N] < 5" = some [("Form/N", "OMISSION_ERROR")] ∧
    run "YearFromDate(/Other/Stamp) + [N] < 2030" = some [("Form/N", "OMISSION_ERROR")] ∧
    run "YearFromDate(/Other/Stamp) + [N] < 2030" [("N", "1")] [("Stamp", "2024-03-05")] =
      some [("Form/N", "VALUE_ERROR")] := by native_decide

example : run "FieldFilled(N) Or [/Other/N] < 5" = some [("Form/N", "OMISSION_ERROR")] ∧
    run "[/Other/N] < 5 And FieldNotFilled(N)" = some [("Form/N", "OMISSION_ERROR")] ∧
    run "[N] < 5 And GroupFilled(/Other)" [] [("Text", "foreign content")] =
      some [("Form/N", "OMISSION_ERROR")] ∧
    run "CurrentRepetition(/Other) + [N] < 5" = some [("Form/N", "OMISSION_ERROR")] := by native_decide

private def roots (text : String) : Option (List String) := do
  let checked ← (checkRule dm .english (rule text)).toOption
  pure checked.condition.core.referencedRoots

example : roots "[/Other/N] + [N] < 5" = some ["Form", "Other"] ∧
    roots "[Sub/A] + [N] < 5" = some ["Form"] ∧
    roots "CurrentRepetition(/Other) + [N] < 5" = some ["Form", "Other"] ∧
    roots "FieldFilled(N) And [/Other/N] < 5" = some ["Form", "Other"] := by native_decide

example : ["[/Other/Rows/N] + [N] < 5", "2 < 3"].all fun text =>
    !(checkRule dm .english (rule text)).isOk := by native_decide

example :
    (match parseText .english "CurrentRepetition(/Other/Rows) + [N] > 1" with
      | .ok parsed => match lowerCondition model ["Form"] false parsed.body with
        | .error refusal => refusal.detail.startsWith
            "A12Kernel.NumericValidationElabError.currentRepetitionSource (A12Kernel.FixedGroupReferenceError.unboundOperandLevel"
        | .ok _ => false
      | .error _ => false) = true := by native_decide

end A12Kernel.Dm.CrossRootValidationLocks
