import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.StringEnumerationBoundaryLocks

open Lean

-- C16's retained Domain_DM fixture separates stored tokens, target patterns and String hints.
-- The source checkpoint owns the Kernel observations; the literal retains the reader boundary.
private def modelSource : String := r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[
{"type":"Group","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Plain","name":"Plain","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"}]}}}},
{"type":"Field","id":"/Form/Labelled","name":"Labelled","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/Text","name":"Text","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/BareOut","name":"BareOut","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/PatternOut","name":"PatternOut","Field":{"fieldType":{"type":"StringType","StringType":{"errorMessage":[{"locale":"en_US","text":"C16 pattern"}],"pattern":"[A-Z]+"}}}},
{"type":"Field","id":"/Form/HintOut","name":"HintOut","Field":{"fieldType":{"type":"StringType","StringType":{"errorMessage":[{"locale":"en_US","text":"C16 pattern"}],"pattern":"[A-Z]+","hintList":[{"locale":"en_US","values":["A","9"]}]}}}},
{"type":"Field","id":"/Form/EnumOut","name":"EnumOut","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"}]}}}},
{"type":"Computation","id":"/Form/BareOutC16","name":"BareOutC16","Computation":{"computedFieldRelPath":"../BareOut","computationAlternatives":[{"operation":"[Plain]"}],"errorMessage":[{"locale":"en_US","text":"C16 computed check"}]}},
{"type":"Computation","id":"/Form/PatternOutC16","name":"PatternOutC16","Computation":{"computedFieldRelPath":"../PatternOut","computationAlternatives":[{"operation":"[Plain]"}],"errorMessage":[{"locale":"en_US","text":"C16 computed check"}]}},
{"type":"Computation","id":"/Form/HintOutC16","name":"HintOutC16","Computation":{"computedFieldRelPath":"../HintOut","computationAlternatives":[{"operation":"[Text]"}],"errorMessage":[{"locale":"en_US","text":"C16 computed check"}]}},
{"type":"Computation","id":"/Form/EnumOutC16","name":"EnumOutC16","Computation":{"computedFieldRelPath":"../EnumOut","computationAlternatives":[{"operation":"[Plain]"}],"errorMessage":[{"locale":"en_US","text":"C16 computed check"}]}}]}}]}}}"#

private def model (identityLabels : Bool := false) : Option DmModel := do
  let source := if identityLabels then modelSource.replace "Alpha" "A" |>.replace "Nine" "9" else modelSource
  (readModel (← (Json.parse source).toOption)).toOption

private def run (token : String) : Option (List String × Bool) := do
  let dm ← model
  if !dm.refusals.isEmpty || dm.computations.length != 4 then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Plain", .str token), ("Labelled", .str token), ("Text", .str token),
    ("BareOut", .str "SEED"), ("PatternOut", .str "SEED"),
    ("HintOut", .str "SEED"), ("EnumOut", .str "A")])])).toOption
  if !data.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let results ← (runModelComputations dm .english world prepared checked).toOption
  let plain ← dm.flat.fields.find? (·.name == "Plain")
  let input ← (checked.read { field := plain.id, path := [] }).toOption
  pure (["BareOut", "PatternOut", "HintOut", "EnumOut"].map (fun name =>
    ((results.find? (·.pointer.endsWith ("/" ++ name))).map (·.outcome)).getD "unchanged"),
    !input.findings.isEmpty)

example : run "A" = some (["value A", "value A", "value A", "unchanged"], false) := by native_decide
example : run "9" = some (["value 9", "errored 9", "errored 9", "value 9"], false) := by native_decide
example : run "Z" = some (["cleared", "cleared", "value Z", "cleared"], true) := by native_decide
example : run "" = some (["cleared", "cleared", "cleared", "cleared"], false) := by native_decide

private def copyRefusal (targetName source : String) (identityLabels : Bool := false) : Option (Bool × String) := do
  let dm ← model identityLabels
  let target ← dm.flat.fields.find? (·.name == targetName)
  let definition : DmComputation := {
    group := ["Form"], name := "Copy", targetRelPath := "../" ++ targetName
    alternatives := [{ operation := "[" ++ source ++ "]", precondition := none }]
    commonPrecondition := none, errorCodesToSuppress := [] }
  let reference : SurfaceFieldPath := { base := .relative 0, groups := [], field := source }
  let code := if target.policy.kind == .string then
    match elaborateStringComputationOperation dm.flat ["Form"] target.id (.field reference) with
    | .ok _ => "admitted"
    | .error error => (error.targetDiagnostic?.map (·.kernelCode)).getD "unclassified"
  else
    match elaborateEnumerationComputation dm.flat ["Form"] target.id (.field (.direct reference)) with
    | .ok _ => "admitted"
    | .error error => ((error.diagnostic?.map (·.kernelCode)).orElse
        (fun _ => error.calculationRefusal?.map (·.catalogKey))).getD "unclassified"
  pure ((lowerComputation dm.flat .english definition).isOk, code)

example : copyRefusal "BareOut" "Plain" = some (true, "admitted") := by native_decide
example : copyRefusal "BareOut" "Labelled" = some (false, "MVK_INVALID_COMPARE_ENUM_TO_STRING") := by native_decide
example : copyRefusal "EnumOut" "Labelled" = some (false, "MVK_INVALID_COMPARE_ENUM_TO_STRING") := by native_decide
example : copyRefusal "BareOut" "Labelled" true = some (true, "admitted") := by native_decide
example : copyRefusal "EnumOut" "Text" = some (false, "MVK_ERROR_INVALID_ENUM_CALCULATION") := by native_decide

end A12Kernel.Dm.StringEnumerationBoundaryLocks
