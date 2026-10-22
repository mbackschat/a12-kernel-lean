import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.CheckedIndexPreliminary

/-! # Reader-to-finding locks for field-owned requiredness

Each row replays one document of the retained real-Kernel capture
`evidence/kernel-30.8.1/captures/field-owned-messages-2026-10-14/` through the DM reader and the
requiredness evaluator, and compares the `mandatoryField` addresses both Kernel strategies observed
under full validation ([checkpoint](../../../docs/sources/message-parameter-rendering-probes.md#src-field-owned-message-producers)).
The [text locks](FieldMessageTextLocks.lean) own the rendered templates; the population replay emits no
row for this capture because its model declares no rule or computation, so these addresses are
compared nowhere else.

The model text below is the retained `R10_DM.json`, re-serialized with one element per line and
otherwise unchanged as JSON. Each fired address is an ERROR of type OMISSION whose error and
fill-to-fix pointers are the address itself, as the capture shows and the evaluator's
`mandatoryAddresses` projection presupposes; sets are compared as sets because no retained
observation fixes an emission order.
-/

namespace A12Kernel.Dm.FieldOwnedRequirednessLocks

open Lean A12Kernel

private def modelText : String := r#"
{"header":{"id":"R10_DM","modelType":"document","modelVersion":"28.4.0","locales":[{"code":"en_US"}],"labels":[],"annotations":[],"modelReferences":[]},"content":{"modelInfo":{"name":"R10_DM","baseYear":"2020"},"modelRoot":{"rootGroups":[{"type":"Group","id":"/P","name":"P","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/P/Other","name":"Other","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/P/q01","name":"q01","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field$ end"}]},"label":[{"locale":"en_US","text":"Label q01"}]}},
{"type":"Field","id":"/P/q02","name":"q02","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field.value$ end"}]}}},
{"type":"Field","id":"/P/q03","name":"q03","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $$ $field$"}]}}},
{"type":"Field","id":"/P/q04","name":"q04","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $Feld$"}]}}},
{"type":"Field","id":"/P/q05","name":"q05","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $BaseYear$"}]}}},
{"type":"Field","id":"/P/q06","name":"q06","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $Other$"}]}}},
{"type":"Field","id":"/P/q07","name":"q07","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field->Cat$"}]}}},
{"type":"Field","id":"/P/q08","name":"q08","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field For \"k\"$"}]}}},
{"type":"Field","id":"/P/q09","name":"q09","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $#P$"}]}}},
{"type":"Field","id":"/P/q10","name":"q10","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field"}]}}},
{"type":"Field","id":"/P/q11","name":"q11","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $FIELD$"}]}}},
{"type":"Field","id":"/P/q12","name":"q12","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field.Wert$"}]}}},
{"type":"Field","id":"/P/q13","name":"q13","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $ field $"}]}}},
{"type":"Field","id":"/P/q14","name":"q14","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"$$"}]}}},
{"type":"Field","id":"/P/q15","name":"q15","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $field$ $field.value$"}]},"label":[{"locale":"en_US","text":"Label q15"}]}},
{"type":"Field","id":"/P/q16","name":"q16","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $Feld.Wert$ end"}]}}},
{"type":"Field","id":"/P/q17","name":"q17","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Req $Feld$ $field$"}]},"label":[{"locale":"en_US","text":"Label q17"}]}},
{"type":"Field","id":"/P/q18","name":"q18","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"A$field$field.value$B"}]},"label":[{"locale":"en_US","text":"Label q18"}]}},
{"type":"Field","id":"/P/q19","name":"q19","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"$field.value$field$"}]},"label":[{"locale":"en_US","text":"Label q19"}]}},
{"type":"Field","id":"/P/q20","name":"q20","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"$Feld$field$"}]},"label":[{"locale":"en_US","text":"Label q20"}]}},
{"type":"Field","id":"/P/q21","name":"q21","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"$field$Feld$"}]},"label":[{"locale":"en_US","text":"Label q21"}]}},
{"type":"Field","id":"/P/q22","name":"q22","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"$field.value$Feld.Wert$"}]},"label":[{"locale":"en_US","text":"Label q22"}]}},
{"type":"Field","id":"/P/q23","name":"q23","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"$Feld.Wert$field$"}]},"label":[{"locale":"en_US","text":"Label q23"}]}},
{"type":"Field","id":"/P/q00","name":"q00","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor"}}},
{"type":"Field","id":"/P/n01","name":"n01","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"B","label":[{"locale":"en_US","text":"Beta"}]}],"errorMessage":[{"locale":"en_US","text":"Enum $field$ end"}]}},"label":[{"locale":"en_US","text":"Label n01"}]}},
{"type":"Field","id":"/P/n02","name":"n02","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"B","label":[{"locale":"en_US","text":"Beta"}]}],"errorMessage":[{"locale":"en_US","text":"Enum $field.value$ end"}]}}}},
{"type":"Group","id":"/P/Rows","name":"Rows","Group":{"repeatability":3,"elements":[
{"type":"Field","id":"/P/Rows/rq","name":"rq","Field":{"fieldType":{"type":"StringType"},"requirednessConfig":{"mode":"absoluteOrRelativeToNextRepAncestor","errorMessage":[{"locale":"en_US","text":"Row $field$ $field.value$"}]},"label":[{"locale":"en_US","text":"Row label"}]}},
{"type":"Field","id":"/P/Rows/rx","name":"rx","Field":{"fieldType":{"type":"StringType"}}}
]}}
]}}]}}}
"#

private def world : World := { now := { epochMillis := 0 } }

private def model? : Option DmModel := do
  let dm ← (readModel (← (Json.parse modelText).toOption)).toOption
  if !dm.refusals.isEmpty then none
  pure dm

/-- The model reads with no refusal and keeps all 25 required declarations, so every row below
measures the evaluator rather than a silently thinned model. -/
example : (model?.map fun dm => (dm.flat.fields.filter (·.requiredness.isSome)).length) = some 25 := by
  native_decide

/-- The 24 fixed required fields `q00`–`q23`, in the capture's pointer order. -/
private def fixedRequired : List (GroupPath × String × List Nat) :=
  (List.range 24).map fun index =>
    (["P"], s!"q{if index < 10 then "0" else ""}{index}", [])

private def addresses (dm : DmModel) (targets : List (GroupPath × String × List Nat)) :
    Option (List CellAddr) :=
  targets.mapM fun (group, name, path) => do
    let field ← dm.flat.fields.find? fun field => field.groupPath == group && field.name == name
    pure { field := field.id, path }

/-- Whether two address lists hold the same duplicate-free set. -/
private def sameSet (actual expected : List CellAddr) : Bool :=
  actual.eraseDups.length == actual.length && expected.eraseDups.length == expected.length &&
    actual.length == expected.length && actual.all expected.contains && expected.all actual.contains

/-- Whether full validation of the document fires `mandatoryField` exactly at the expected cells. -/
private def holds (document : String) (expected : List (GroupPath × String × List Nat)) : Bool :=
  (do
    let dm ← model?
    let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
    let raw ← (readDocument dm (← (Json.parse document).toOption)).toOption
    if !raw.refusals.isEmpty then none
    let checked ← (checkDocument prepared "en_US" raw.data).toOption
    let full ← checked.fullRequiredEvaluations.toOption
    pure (sameSet (RequiredEvaluation.mandatoryAddresses full) (← addresses dm expected))).getD false

/-- Row `empty`: every fixed required field draws, the template-less `q00` included, and the row field
`rq` stays silent because `Rows` has no instance. -/
example : holds r#"{"P":{"Other":"o"}}"# fixedRequired = true := by native_decide

/-- Row `bad`: the first row, which lacks `rq`, draws beside every fixed field, and the second, which
holds it, does not; the Enumeration cells' value findings are not requiredness findings. -/
example : holds r#"{"P":{"Other":"o","Rows":[{"rx":"1"},{"rq":"v","rx":"2"}],"n01":"Z","n02":"Z"}}"#
    ((["P", "Rows"], "rq", [1]) :: fixedRequired) = true := by native_decide

/-- Row `full`: every required cell filled, and the Enumerations given valid values, draws nothing. -/
example : holds r#"{"P":{"Other":"o","q00":"x","Rows":[{"rq":"v","rx":"1"}],"q01":"x","q02":"x","q03":"x","q04":"x","q05":"x","q06":"x","q07":"x","q08":"x","q09":"x","q10":"x","q11":"x","q12":"x","q13":"x","q14":"x","q15":"x","q16":"x","q17":"x","q18":"x","q19":"x","q20":"x","q21":"x","q22":"x","q23":"x","n01":"A","n02":"A"}}"#
    [] = true := by native_decide

end A12Kernel.Dm.FieldOwnedRequirednessLocks
