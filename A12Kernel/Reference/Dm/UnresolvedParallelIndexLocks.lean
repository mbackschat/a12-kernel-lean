import A12Kernel.Reference.Dm.ParallelValidation

/-! # A parallel iteration over an index naming no field

Kernel 30.8.1 built no model whose group nominated an index field naming none of its children. Kernel 31.1.1
builds it, the declaration drawing `MVK_INVALID_INDEX_FIELD`, and a rule joining that group with a keyed
partner settles the walk on the declared index and fails its name stage with `MVK_INDEX_FIELD_INVALID`,
whichever side declares it and on a value read as on a presence read. The same rule with the name resolved
is admitted. The [capture](../../../evidence/kernel-31.1.1/captures/unresolved-parallel-index-2026-11-05/)
measures every row below; each Kernel row also carries the declaration's own class, which the rule check
does not judge.
-/

namespace A12Kernel.Dm.UnresolvedParallelIndexLocks

open Lean A12Kernel

/-- `Et` holding the repeatable `Rows`, indexed by its Number `Key`, and the repeatable `Side`, nominating
`sideIndex` as its index beside its own Number `Key` and String `Val`. -/
private def model (sideIndex : String) : Except String Json :=
  Json.parse (r#"{"header":{"id":"U_DM","modelType":"document","modelVersion":"29.4.0","locales":[{"code":"en_US"}]},
"content":{"modelInfo":{"name":"U_DM"},"modelConfig":{"timeZone":"Europe/Berlin","conditionLanguage":{"code":"en_US"}},
"modelRoot":{"rootGroups":[{"type":"Group","id":"/Et","name":"Et","Group":{"repeatability":5,"elements":[
{"type":"Group","id":"/Et/Rows","name":"Rows","Group":{"repeatability":5,"indexFieldName":"Key","elements":[
{"type":"Field","id":"/Et/Rows/Key","name":"Key","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Et/Rows/Note","name":"Note","Field":{"fieldType":{"type":"StringType"}}}]}},
{"type":"Group","id":"/Et/Side","name":"Side","Group":{"repeatability":5,"indexFieldName":""# ++ sideIndex ++ r#"","elements":[
{"type":"Field","id":"/Et/Side/Key","name":"Key","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Et/Side/Val","name":"Val","Field":{"fieldType":{"type":"StringType"}}}]}}]}}]}}}"#)

/-- The rule's admission: `none` when admitted, else its class, or `"unclassed"` for a refusal naming none. -/
private def ruleClass (sideIndex : String) (group : List String) (errorPath condition : String) :
    Option String :=
  match model sideIndex >>= readModel with
  | .error _ => some "no model"
  | .ok dm =>
      let rule : DmRule := { group, name := "R", severity := "ERROR", errorCode := "R", condition
                             errorEntityRelPath := errorPath }
      match checkValidationRule dm .english rule with
      | .ok _ => none
      | .error refusal => some (refusal.kernelClass?.getD "unclassed")

example :
    ruleClass "Nokey" ["Et", "Rows"] "../Note" "FieldFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val)" =
      some "MVK_INDEX_FIELD_INVALID" ∧
    ruleClass "Key" ["Et", "Rows"] "../Note" "FieldFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val)" = none ∧
    ruleClass "Nokey" ["Et", "Rows"] "../Note" "FieldFilled(/Et/Rows/Note)" = none ∧
    ruleClass "Nokey" ["Et", "Side"] "../Val" "FieldFilled(/Et/Side/Val) And FieldFilled(/Et/Rows/Note)" =
      some "MVK_INDEX_FIELD_INVALID" ∧
    ruleClass "Nokey" ["Et", "Rows"] "../Note" "FieldFilled(/Et/Rows/Note) And [/Et/Side/Key] > 0" =
      some "MVK_INDEX_FIELD_INVALID" := by
  native_decide

end A12Kernel.Dm.UnresolvedParallelIndexLocks
