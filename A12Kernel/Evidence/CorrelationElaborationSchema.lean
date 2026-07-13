import Lean.Data.Json

/-! # A12Kernel.Evidence.CorrelationElaborationSchema — static correlation transport

This closed projection carries only the full model identity plus structured model and rule input needed to replay four retained authoring observations. Expected diagnostic codes remain solely in the external observations referenced by `caseRef`.
-/

namespace A12Kernel.Evidence.CorrelationElaboration

open Lean

structure RepeatableGroupSpec where
  level : Nat
  path : List String
  deriving Repr, DecidableEq

structure NumberFieldSpec where
  id : Nat
  groupLevel : Nat
  name : String
  scale : Nat
  signed : Bool
  deriving Repr, DecidableEq

structure RelativeFieldPathSpec where
  groups : List String
  field : String
  deriving Repr, DecidableEq

structure RelativeStarFieldPathSpec where
  groupsBeforeStar : List String
  starredGroup : String
  field : String
  deriving Repr, DecidableEq

inductive OriginSpec where
  | inner
  | outer
  deriving Repr, DecidableEq

inductive ComparisonOpSpec where
  | equal
  | lessThan
  deriving Repr, DecidableEq

structure NumberRefSpec where
  origin : OriginSpec
  field : RelativeFieldPathSpec
  deriving Repr, DecidableEq

structure HavingSpec where
  comparison : ComparisonOpSpec
  left : NumberRefSpec
  right : NumberRefSpec
  deriving Repr, DecidableEq

structure RuleSpec where
  declaringGroup : List String
  errorField : RelativeFieldPathSpec
  guardField : RelativeFieldPathSpec
  valueField : RelativeStarFieldPathSpec
  having : HavingSpec
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  modelSha256 : String
  groups : List RepeatableGroupSpec
  fields : List NumberFieldSpec
  rule : RuleSpec
  deriving Repr, DecidableEq

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  cases : List CaseSpec
  deriving Repr, DecidableEq

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def parseGroup (json : Json) : Except String RepeatableGroupSpec := do
  pure { level := ← member json "level", path := ← member json "path" }

private def parseField (json : Json) : Except String NumberFieldSpec := do
  pure {
    id := ← member json "id"
    groupLevel := ← member json "groupLevel"
    name := ← member json "name"
    scale := ← member json "scale"
    signed := ← member json "signed" }

private def parseRelativeField (json : Json) : Except String RelativeFieldPathSpec := do
  pure { groups := ← member json "groups", field := ← member json "field" }

private def parseRelativeStarField (json : Json) :
    Except String RelativeStarFieldPathSpec := do
  pure {
    groupsBeforeStar := ← member json "groupsBeforeStar"
    starredGroup := ← member json "starredGroup"
    field := ← member json "field" }

private def parseOrigin (json : Json) : Except String OriginSpec := do
  let name : String ← member json "origin"
  match name with
  | "inner" => pure .inner
  | "outer" => pure .outer
  | other => throw s!"unsupported correlation-elaboration origin '{other}'"

private def parseComparison (json : Json) : Except String ComparisonOpSpec := do
  let name : String ← member json "comparison"
  match name with
  | "equal" => pure .equal
  | "lessThan" => pure .lessThan
  | other => throw s!"unsupported correlation-elaboration comparison '{other}'"

private def parseNumberRef (json : Json) : Except String NumberRefSpec := do
  pure {
    origin := ← parseOrigin json
    field := ← parseRelativeField (← json.getObjVal? "field") }

private def parseHaving (json : Json) : Except String HavingSpec := do
  pure {
    comparison := ← parseComparison json
    left := ← parseNumberRef (← json.getObjVal? "left")
    right := ← parseNumberRef (← json.getObjVal? "right") }

private def parseRule (json : Json) : Except String RuleSpec := do
  pure {
    declaringGroup := ← member json "declaringGroup"
    errorField := ← parseRelativeField (← json.getObjVal? "errorField")
    guardField := ← parseRelativeField (← json.getObjVal? "guardField")
    valueField := ← parseRelativeStarField (← json.getObjVal? "valueField")
    having := ← parseHaving (← json.getObjVal? "having") }

private def parseCase (json : Json) : Except String CaseSpec := do
  let operation : String ← member json "operation"
  if operation != "elaborateSingleCorrelation" then
    throw s!"unsupported correlation-elaboration evidence operation '{operation}'"
  let groupJson : List Json ← member json "groups"
  let fieldJson : List Json ← member json "fields"
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    modelSha256 := ← member json "modelSha256"
    groups := ← groupJson.mapM parseGroup
    fields := ← fieldJson.mapM parseField
    rule := ← parseRule (← json.getObjVal? "rule") }

def Bundle.fromJson (json : Json) : Except String Bundle := do
  let caseJson : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    cases := ← caseJson.mapM parseCase }

end A12Kernel.Evidence.CorrelationElaboration
