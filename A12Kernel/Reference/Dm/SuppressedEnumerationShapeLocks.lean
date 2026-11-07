import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.ComputeMessages
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Every operation shape into an Enumeration target under the calculation's preamble

The calculation's domain check refuses each alternative's operation by its shape alone, so a preamble naming
`MVK_ERROR_INVALID_ENUM_CALCULATION` admits all of them and the target judges whatever text they produce
(spec/09 §4.3). The model, its thirteen computations and the five documents are Kernel 31.3.1's, both
strategies agreeing, and every expectation is that capture's own verdict or change
([checkpoint](../../../docs/sources/kernel-31-calibration-probes.md#src-suppressed-enum-calculation-shapes)):
a fixed copy, String and mixed first-filled lists, a concatenation, a keyed String column, `FieldValueAsString`,
a starred String walk and an Enumeration copy beyond the domain; a row target's copy, first-filled list and
concatenation; and two key-joined partner copies. The generated validation rules of the same capture replay in
the population gate.
-/

namespace A12Kernel.Dm.SuppressedEnumerationShapeLocks

open Lean

private def modelSource (preamble : String) : String :=
  r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[{"type":"Group","id":"/Form","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Text","name":"Text","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Text2","name":"Text2","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Wide","name":"Wide","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"},{"value":"B"}]}}}},
{"type":"Field","id":"/Form/Count","name":"Count","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Form/OutA","name":"OutA","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutB","name":"OutB","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutC","name":"OutC","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutD","name":"OutD","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutE","name":"OutE","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutF","name":"OutF","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutG","name":"OutG","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutH","name":"OutH","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Field","id":"/Form/OutI","name":"OutI","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Group","id":"/Form/Cats","name":"Cats","Group":{"repeatability":3,"elements":[{"type":"Field","id":"/Form/Cats/Key","name":"Key","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Cats/Code","name":"Code","Field":{"fieldType":{"type":"StringType"}}}],"indexFieldName":"Key"}},
{"type":"Group","id":"/Form/Lines","name":"Lines","Group":{"repeatability":3,"elements":[{"type":"Field","id":"/Form/Lines/LText","name":"LText","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Lines/LOut1","name":"LOut1","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},{"type":"Field","id":"/Form/Lines/LOut2","name":"LOut2","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},{"type":"Field","id":"/Form/Lines/LOut3","name":"LOut3","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},{"type":"Computation","id":"/Form/Lines/r01","name":"r01","Computation":{"computedFieldRelPath":"../LOut1","computationAlternatives":[{"operation":"[LText]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},{"type":"Computation","id":"/Form/Lines/r02","name":"r02","Computation":{"computedFieldRelPath":"../LOut2","computationAlternatives":[{"operation":"FirstFilledValue(LText, /Form/Text)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},{"type":"Computation","id":"/Form/Lines/r03","name":"r03","Computation":{"computedFieldRelPath":"../LOut3","computationAlternatives":[{"operation":"[LText] + \"x\""}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}}]}},
{"type":"Group","id":"/Form/Demand","name":"Demand","Group":{"repeatability":3,"elements":[{"type":"Field","id":"/Form/Demand/Dept","name":"Dept","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Demand/DLabel","name":"DLabel","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Demand/DCode","name":"DCode","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"},{"value":"B"}]}}}}],"indexFieldName":"Dept"}},
{"type":"Group","id":"/Form/Supply","name":"Supply","Group":{"repeatability":3,"elements":[{"type":"Field","id":"/Form/Supply/Dept","name":"Dept","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Supply/SOut1","name":"SOut1","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},{"type":"Field","id":"/Form/Supply/SOut2","name":"SOut2","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},{"type":"Computation","id":"/Form/Supply/j01","name":"j01","Computation":{"computedFieldRelPath":"../SOut1","computationAlternatives":[{"operation":"[/Form/Demand/DLabel]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},{"type":"Computation","id":"/Form/Supply/j02","name":"j02","Computation":{"computedFieldRelPath":"../SOut2","computationAlternatives":[{"operation":"[/Form/Demand/DCode]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}}],"indexFieldName":"Dept"}},
{"type":"Computation","id":"/Form/c01","name":"c01","Computation":{"computedFieldRelPath":"../OutA","computationAlternatives":[{"operation":"[Text]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c02","name":"c02","Computation":{"computedFieldRelPath":"../OutB","computationAlternatives":[{"operation":"FirstFilledValue(Text, Wide)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c03","name":"c03","Computation":{"computedFieldRelPath":"../OutC","computationAlternatives":[{"operation":"FirstFilledValue(Text, Text2)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c04","name":"c04","Computation":{"computedFieldRelPath":"../OutD","computationAlternatives":[{"operation":"[Text] + [Text2]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c05","name":"c05","Computation":{"computedFieldRelPath":"../OutE","computationAlternatives":[{"operation":"[Cats/Code For \"k1\"]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c06","name":"c06","Computation":{"computedFieldRelPath":"../OutF","computationAlternatives":[{"operation":"FieldValueAsString(Count)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c07","name":"c07","Computation":{"computedFieldRelPath":"../OutG","computationAlternatives":[{"operation":"FirstFilledValue(Lines*/LText)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}},
{"type":"Computation","id":"/Form/c09","name":"c09","Computation":{"computedFieldRelPath":"../OutI","computationAlternatives":[{"operation":"[Wide]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"PREAMBLE"}}]}}]}}}"#
    |>.replace "PREAMBLE" preamble

private def suppressCalculation : String := "@SuppressWarning(MVK_ERROR_INVALID_ENUM_CALCULATION)"

private def model (preamble := suppressCalculation) : Option DmModel := do
  let dm ← (readModel (checkedEntryFrame (← (Json.parse (modelSource preamble)).toOption))).toOption
  if dm.refusals.isEmpty then some dm else none

private def verdicts (preamble := suppressCalculation) : Option (List (String × String)) := do
  let dm ← model preamble
  pure (dm.computations.map fun computation => (computation.name,
    match checkComputation dm .english computation with
    | .ok _ => "admitted"
    | .error refusal => refusal.kernelClass?.getD s!"unclassified {refusal.detail}"))

private def run (document : String) : Option (List (String × String)) := do
  let dm ← model
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let data ← (readDocument dm (← (Json.parse document).toOption)).toOption
  if !data.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let (results, _) ← (runModelComputationsWithMessages dm .english world prepared checked).toOption
  pure (results.map fun result => (result.pointer, result.outcome))

-- The calculation refuses every shape that is not a plain read of a compatible Enumeration, a constant or a
-- compatible first-filled list; the preamble lifts that class alone, and the Number source's comparison class
-- stands either way (`c08`, outside this model).
private def computationNames : List String :=
  ["r01", "r02", "r03", "j01", "j02", "c01", "c02", "c03", "c04", "c05", "c06", "c07", "c09"]

example : verdicts = some (computationNames.map (·, "admitted")) := by
  native_decide

example : verdicts (preamble := "") =
    some (computationNames.map (·, "MVK_ERROR_INVALID_ENUM_CALCULATION")) := by
  native_decide

-- Declared tokens on every shape: each is stored; a row without its `"x"` suffix and a joined row without a partner are not.
example : run r#"{"Form":{"OutA":"A","OutB":"A","OutC":"A","OutD":"A","OutE":"A","OutF":"A","OutG":"A","OutI":"A","Text":"9","Text2":"","Wide":"A","Count":"9","Cats":[{"Key":"k1","Code":"9"}],"Lines":[{"LOut1":"A","LOut2":"A","LOut3":"A","LText":"9"},{"LOut1":"A","LOut2":"A","LOut3":"A","LText":"Z"}],"Demand":[{"Dept":"d1","DLabel":"9","DCode":"A"}],"Supply":[{"Dept":"d1","SOut1":"A","SOut2":"A"},{"Dept":"d9","SOut1":"A","SOut2":"A"}]}}"# = some [("Form/Lines/LOut1", "value 9"),
      ("Form/Lines[2]/LOut1", "errored Z"),
      ("Form/Lines/LOut2", "value 9"),
      ("Form/Lines[2]/LOut2", "errored Z"),
      ("Form/Lines/LOut3", "errored 9x"),
      ("Form/Lines[2]/LOut3", "errored Zx"),
      ("Form/Supply/SOut1", "value 9"),
      ("Form/Supply[2]/SOut1", "cleared"),
      ("Form/Supply[2]/SOut2", "cleared"),
      ("Form/OutA", "value 9"),
      ("Form/OutB", "value 9"),
      ("Form/OutC", "value 9"),
      ("Form/OutD", "value 9"),
      ("Form/OutE", "value 9"),
      ("Form/OutF", "value 9"),
      ("Form/OutG", "value 9")] := by
  native_decide

-- A declared value's label on every shape errors the target with that text; `FieldValueAsString` offers the Number's text.
example : run r#"{"Form":{"OutA":"A","OutB":"A","OutC":"A","OutD":"A","OutE":"A","OutF":"A","OutG":"A","OutI":"A","Text":"Alpha","Text2":"","Wide":"B","Count":"5","Cats":[{"Key":"k1","Code":"Alpha"}],"Lines":[{"LOut1":"A","LOut2":"A","LOut3":"A","LText":"Alpha"}],"Demand":[{"Dept":"d1","DLabel":"Alpha","DCode":"B"}],"Supply":[{"Dept":"d1","SOut1":"A","SOut2":"A"}]}}"# = some [("Form/Lines/LOut1", "errored Alpha"),
      ("Form/Lines/LOut2", "errored Alpha"),
      ("Form/Lines/LOut3", "errored Alphax"),
      ("Form/Supply/SOut1", "errored Alpha"),
      ("Form/Supply/SOut2", "errored B"),
      ("Form/OutA", "errored Alpha"),
      ("Form/OutB", "errored Alpha"),
      ("Form/OutC", "errored Alpha"),
      ("Form/OutD", "errored Alpha"),
      ("Form/OutE", "errored Alpha"),
      ("Form/OutF", "errored 5"),
      ("Form/OutG", "errored Alpha"),
      ("Form/OutI", "errored B")] := by
  native_decide

-- An undeclared text on every shape errors the target with that text.
example : run r#"{"Form":{"OutA":"A","OutB":"A","OutC":"A","OutD":"A","OutE":"A","OutF":"A","OutG":"A","OutI":"A","Text":"Z","Text2":"","Wide":"B","Count":"77","Cats":[{"Key":"k1","Code":"Z"}],"Lines":[{"LOut1":"A","LOut2":"A","LOut3":"A","LText":"Z"}],"Demand":[{"Dept":"d1","DLabel":"Z","DCode":"B"}],"Supply":[{"Dept":"d1","SOut1":"A","SOut2":"A"}]}}"# = some [("Form/Lines/LOut1", "errored Z"),
      ("Form/Lines/LOut2", "errored Z"),
      ("Form/Lines/LOut3", "errored Zx"),
      ("Form/Supply/SOut1", "errored Z"),
      ("Form/Supply/SOut2", "errored B"),
      ("Form/OutA", "errored Z"),
      ("Form/OutB", "errored Z"),
      ("Form/OutC", "errored Z"),
      ("Form/OutD", "errored Z"),
      ("Form/OutE", "errored Z"),
      ("Form/OutF", "errored 77"),
      ("Form/OutG", "errored Z"),
      ("Form/OutI", "errored B")] := by
  native_decide

-- Empty sources clear every target but a concatenation with a literal part, whose `"x"` the target refuses.
example : run r#"{"Form":{"OutA":"A","OutB":"A","OutC":"A","OutD":"A","OutE":"A","OutF":"A","OutG":"A","OutI":"A","Lines":[{"LOut1":"A","LOut2":"A","LOut3":"A"}],"Supply":[{"Dept":"d1","SOut1":"A","SOut2":"A"}]}}"# = some [("Form/Lines/LOut1", "cleared"),
      ("Form/Lines/LOut2", "cleared"),
      ("Form/Lines/LOut3", "errored x"),
      ("Form/Supply/SOut1", "cleared"),
      ("Form/Supply/SOut2", "cleared"),
      ("Form/OutA", "cleared"),
      ("Form/OutB", "cleared"),
      ("Form/OutC", "cleared"),
      ("Form/OutD", "cleared"),
      ("Form/OutE", "cleared"),
      ("Form/OutF", "cleared"),
      ("Form/OutG", "cleared"),
      ("Form/OutI", "cleared")] := by
  native_decide

-- First-filled scans skip an empty earlier member and judge the one they select: a later Enumeration member's undeclared `B` errors the target rather than falling through.
example : run r#"{"Form":{"OutA":"A","OutB":"A","OutC":"A","OutD":"A","OutE":"A","OutF":"A","OutG":"A","OutI":"A","Text2":"9","Wide":"B","Lines":[{"LOut1":"A","LOut2":"A","LOut3":"A"},{"LOut1":"A","LOut2":"A","LOut3":"A","LText":"9"}]}}"# = some [("Form/Lines/LOut1", "cleared"),
      ("Form/Lines[2]/LOut1", "value 9"),
      ("Form/Lines/LOut2", "cleared"),
      ("Form/Lines[2]/LOut2", "value 9"),
      ("Form/Lines/LOut3", "errored x"),
      ("Form/Lines[2]/LOut3", "errored 9x"),
      ("Form/OutA", "cleared"),
      ("Form/OutB", "errored B"),
      ("Form/OutC", "value 9"),
      ("Form/OutD", "value 9"),
      ("Form/OutE", "cleared"),
      ("Form/OutF", "cleared"),
      ("Form/OutG", "value 9"),
      ("Form/OutI", "errored B")] := by
  native_decide

/- The preamble lifts the calculation's class alone: a first-filled list naming its own target, in either
position, answers the self-read under it, and a key-joined copy without it answers the calculation's class
(Kernel 31.3.1, computations `f2`, `f4` and `j2` of the
[precedence batch](../../../docs/sources/kernel-31-calibration-probes.md#src-computation-precedence)). -/
private def precedenceVerdicts : Option (List (String × String)) := do
  let json ← (Json.parse (r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[{"type":"Group","id":"/Form","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Text","name":"Text","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/O2","name":"O2","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"}]}}}},
{"type":"Field","id":"/Form/O4","name":"O4","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"}]}}}},
{"type":"Computation","id":"/Form/f2","name":"f2","Computation":{"computedFieldRelPath":"../O2","computationAlternatives":[{"operation":"FirstFilledValue(Text, O2)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"@SuppressWarning(MVK_ERROR_INVALID_ENUM_CALCULATION)"}},
{"type":"Computation","id":"/Form/f4","name":"f4","Computation":{"computedFieldRelPath":"../O4","computationAlternatives":[{"operation":"FirstFilledValue(O4, Text)"}],"errorMessage":[{"locale":"en_US","text":"m"}],"additionalParserInformation":"@SuppressWarning(MVK_ERROR_INVALID_ENUM_CALCULATION)"}},
{"type":"Group","id":"/Form/Demand","name":"Demand","Group":{"repeatability":3,"elements":[{"type":"Field","id":"/Form/Demand/Dept","name":"Dept","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Demand/DLabel","name":"DLabel","Field":{"fieldType":{"type":"StringType"}}}],"indexFieldName":"Dept"}},
{"type":"Group","id":"/Form/Supply","name":"Supply","Group":{"repeatability":3,"elements":[{"type":"Field","id":"/Form/Supply/Dept","name":"Dept","Field":{"fieldType":{"type":"StringType"}}},{"type":"Field","id":"/Form/Supply/SOut2","name":"SOut2","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"}]}}}},{"type":"Computation","id":"/Form/Supply/j2","name":"j2","Computation":{"computedFieldRelPath":"../SOut2","computationAlternatives":[{"operation":"FirstFilledValue(/Form/Demand/DLabel, /Form/Text)"}],"errorMessage":[{"locale":"en_US","text":"m"}]}}],"indexFieldName":"Dept"}}]}}]}}}"#)).toOption
  let dm ← (readModel (checkedEntryFrame json)).toOption
  if !dm.refusals.isEmpty then none
  pure (dm.computations.map fun computation => (computation.name,
    match checkComputation dm .english computation with
    | .ok _ => "admitted"
    | .error refusal => refusal.kernelClass?.getD s!"unclassified {refusal.detail}"))

example : precedenceVerdicts = some [("f2", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD"),
    ("f4", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD"), ("j2", "MVK_ERROR_INVALID_ENUM_CALCULATION")] := by
  native_decide

end A12Kernel.Dm.SuppressedEnumerationShapeLocks
