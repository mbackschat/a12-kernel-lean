import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # An unprefixed read in a filter body resolves as every condition read does

From the rule's group first, then by short name where the model allows it; the filter opens no resolution scope
of its own. The eight cells are Kernel 31.3.1's
([checkpoint](../../../docs/sources/having-filter-probes.md#src-having-body-short-name)): they separate the
account in which a body read resolves from the filtered group, which admits `[Note]` with short names off and
reads `[Tag]` per row.
-/

namespace A12Kernel.Dm.HavingBodyResolutionLocks

open Lean

private def modelSource (shortNames : Bool) : String :=
  r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"},"fieldRefByShortNameAllowed":FLAG},"modelRoot":{"rootGroups":[
{"type":"Group","name":"Policy","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Policy/Premium","name":"Premium","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Policy/Tag","name":"Tag","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Group","id":"/Policy/Lines","name":"Lines","Group":{"repeatability":5,"elements":[
{"type":"Field","id":"/Policy/Lines/Amount","name":"Amount","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Policy/Lines/Note","name":"Note","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Policy/Lines/Tag","name":"Tag","Field":{"fieldType":{"type":"StringType"}}}]}}]}}]}}}"#
    |>.replace "FLAG" (toString shortNames)

/-- The verdict of a `/Policy` rule `Sum(Lines*/Amount Having [body] == "x") < [Premium]`. -/
private def verdict (shortNames : Bool) (body : String) : Option String := do
  let dm ← (readModel (checkedEntryFrame (← (Json.parse (modelSource shortNames)).toOption))).toOption
  if !dm.refusals.isEmpty then none
  match checkValidationRule dm .english {
    group := ["Policy"], name := "R", errorEntityRelPath := "../Premium", errorCode := "R", severity := "ERROR"
    condition := s!"Sum(Lines*/Amount Having [{body}] == \"x\") < [Premium]" } with
  | .ok _ => pure "admitted"
  | .error refusal => pure (refusal.kernelClass?.getD "unclassified")

example :
    verdict false "Note" = some "MVK_INVALID_ENTITY" &&
    verdict true "Note" = some "admitted" &&
    verdict false "Lines/Note" = some "admitted" &&
    verdict true "Lines/Note" = some "admitted" &&
    verdict false "Tag" = some "MVK_NO_ITERATION_FOR_WILDCARD" &&
    verdict true "Tag" = some "MVK_NO_ITERATION_FOR_WILDCARD" &&
    verdict false "Nope" = some "MVK_INVALID_ENTITY" &&
    verdict true "Nope" = some "MVK_INVALID_ENTITY" := by
  native_decide

end A12Kernel.Dm.HavingBodyResolutionLocks
