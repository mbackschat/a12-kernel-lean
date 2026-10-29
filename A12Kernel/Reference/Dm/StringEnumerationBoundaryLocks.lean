import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.EntryFrameFixture

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
  (readModel (checkedEntryFrame (← (Json.parse source).toOption))).toOption

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

private def firstFilledRun (operation text token : String) : Option (List String) := do
  let dm ← model
  let definition : DmComputation := {
    group := ["Form"], name := "First", targetRelPath := "../BareOut"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }
  let dm := { dm with computations := [definition] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Text", .str text), ("Labelled", .str token), ("Plain", .str "9"), ("BareOut", .str "SEED")])])).toOption
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let results ← (runModelComputations dm .english world prepared checked).toOption
  pure (results.map (·.outcome))

example : firstFilledRun "FirstFilledValue(Text,Labelled)" "" "A" = some ["value A"] := by native_decide
example : firstFilledRun "FirstFilledValue(Labelled,Text)" "T" "A" = some ["value A"] := by native_decide
example : firstFilledRun "FirstFilledValue(Text,Labelled)" "T" "invalid" = some ["value T"] := by native_decide
example : firstFilledRun "FirstFilledValue(Labelled,Text)" "T" "invalid" = some ["cleared"] := by native_decide

private def firstFilledCarrierModel : Option DmModel := do
  let dm ← model
  let text ← dm.flat.fields.find? (·.name == "Text")
  let choice ← dm.flat.fields.find? (·.name == "Labelled")
  let domain ← choice.enumeration
  let choice := { choice with enumeration := some { domain with categories := [{ name := "Label", tokens := ["K", "D"] }] } }
  let fixed (prototype : FlatFieldDecl) (id : FieldId) (name : String) :=
    { prototype with id, name, groupPath := ["Form"] }
  let row (prototype : FlatFieldDecl) (id : FieldId) (name : String) :=
    { prototype with id, name, groupPath := ["Form", "Rows"], repeatableScope := [10] }
  pure { dm with
    flat := {
      fields := [fixed text 1 "Text", fixed choice 2 "Choice", fixed choice 3 "Choice2",
        fixed text 4 "Out", fixed choice 5 "EnumOut", row text 6 "Out", row choice 7 "EnumOut"]
      repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
    computations := [] }

private def firstFilledDefinition (target operation : String) : DmComputation := {
  group := ["Form"], name := "First", targetRelPath := "../" ++ target
  commonPrecondition := none, alternatives := [{ precondition := none, operation }]
  errorCodesToSuppress := [] }

private def carrierRefusal (target operation : String) : Option String := do
  let dm ← firstFilledCarrierModel
  pure (match lowerComputation dm.flat .english (firstFilledDefinition target operation) with
    | .ok _ => "admitted"
    | .error refusal => refusal.detail)

private def carrierStepRefusal (target operation : String) : Option String := do
  let dm ← firstFilledCarrierModel
  let target ← dm.flat.fields.find? (fun field => field.path == ["Form"] ++ target.splitOn "/")
  let expression ← (parseText .english operation).toOption
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted"
    | .error refusal => refusal.detail
  pure (if target.repeatableScope.isEmpty then
    report (lowerDocumentStep dm.flat ["Form"] target false expression.body)
  else report (lowerRowStep dm.flat ["Form"] target false expression.body))

private def carrierRun (target operation text first second : String) : Option (List String) := do
  let dm ← firstFilledCarrierModel
  let dm := { dm with computations := [firstFilledDefinition target operation] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let row := Json.mkObj [("Out", .str "SEED"), ("EnumOut", .str "9")]
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Text", .str text), ("Choice", .str first), ("Choice2", .str second),
    ("Out", .str "SEED"), ("EnumOut", .str "9"), ("Rows", .arr #[row, row])])])).toOption
  if !data.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  pure ((← (runModelComputations dm .english world prepared checked).toOption).map (·.outcome))

example : ["Out", "Rows/Out"].all (fun target =>
    carrierRun target "FirstFilledValue(Choice,Choice2)" "" "A" "9" ==
      some (if target == "Out" then ["value A"] else ["value A", "value A"]) &&
    carrierRun target "FirstFilledValue(Choice,Choice2)" "" "" "9" ==
      some (if target == "Out" then ["value 9"] else ["value 9", "value 9"]) &&
    carrierRun target "FirstFilledValue(Text,Choice->Label)" "" "A" "9" ==
      some (if target == "Out" then ["value K"] else ["value K", "value K"]) &&
    carrierRun target "FirstFilledValue(Text,Choice->Label)" "T" "invalid" "9" ==
      some (if target == "Out" then ["value T"] else ["value T", "value T"]) &&
    carrierRun target "FirstFilledValue(Text,Choice->Label)" "" "invalid" "9" ==
      some (if target == "Out" then ["cleared"] else ["cleared", "cleared"]) &&
    carrierRun target "FirstFilledValue(Choice,Choice2)" "" "" "" ==
      some (if target == "Out" then ["cleared"] else ["cleared", "cleared"])) = true := by native_decide

example : ["EnumOut", "Rows/EnumOut"].all (fun target =>
    carrierRefusal target "FirstFilledValue(Text,Choice)" == some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    carrierRefusal target "FirstFilledValue(Choice,Text)" == some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    carrierRefusal target "FirstFilledValue(Choice,Choice2)" == some "admitted" &&
    carrierStepRefusal target "FirstFilledValue(Text,Choice)" == some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    carrierStepRefusal target "FirstFilledValue(Choice,Text)" == some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    carrierStepRefusal target "FirstFilledValue(Choice,Choice2)" == some "admitted") = true := by native_decide

example : ["EnumOut", "Rows/EnumOut"].all (fun target =>
    carrierRun target "FirstFilledValue(Choice,Choice2)" "" "A" "9" ==
      some (if target == "EnumOut" then ["value A"] else ["value A", "value A"])) = true := by native_decide

example : ["EnumOut", "Rows/EnumOut"].all (fun target =>
    carrierRefusal target "FirstFilledValue(/Form/Rows*/Out)" == some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    carrierStepRefusal target "FirstFilledValue(/Form/Rows*/Out)" == some "MVK_ERROR_INVALID_ENUM_CALCULATION") = true := by native_decide

example : carrierRefusal "Out" "FirstFilledValue(Rows*/Out)" = some "admitted" := by native_decide

end A12Kernel.Dm.StringEnumerationBoundaryLocks
