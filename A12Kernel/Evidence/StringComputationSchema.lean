import Lean.Data.Json

/-! # A12Kernel.Evidence.StringComputationSchema — String-computation evidence transport

The closed projection carries exactly the resolved String fields, expression trees, source cells, prior target states, and retained artifact identities needed by the first computation capsule. Expected deltas remain solely in the external case artifacts.
-/

namespace A12Kernel.Evidence.StringComputation

open Lean

structure FieldSpec where
  id : Nat
  groups : List String
  name : String
  deriving Repr, DecidableEq

inductive ExprSpec where
  | field (fieldId : Nat)
  | literal (value : String)
  | concat (left right : ExprSpec)
  deriving Repr, DecidableEq

structure ModelSpec where
  id : String
  modelRef : String
  modelSha256 : String
  declaringGroup : List String
  fields : List FieldSpec
  computationName : String
  targetFieldId : Nat
  targetRelPath : String
  targetPointer : String
  expression : ExprSpec
  deriving Repr, DecidableEq

inductive CellStateSpec where
  | empty
  | string (value : String)
  deriving Repr, DecidableEq

structure CellSpec where
  fieldId : Nat
  state : CellStateSpec
  deriving Repr, DecidableEq

inductive TargetStateSpec where
  | empty
  | string (value : String)
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  caseSha256 : String
  modelId : String
  cells : List CellSpec
  priorTarget : TargetStateSpec
  hasContent : Bool
  deriving Repr, DecidableEq

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  captureRef : String
  captureSha256 : String
  sourceRevision : String
  models : List ModelSpec
  cases : List CaseSpec
  deriving Repr, DecidableEq

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def objectNames (context : String) (json : Json) : Except String (List String) :=
  match json.getObj? with
  | .ok object => pure <| object.toList.map (fun entry => entry.1)
  | .error _ => throw s!"{context} must be an object"

private def hasDuplicate [BEq α] : List α → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def sameInventory (actual expected : List String) : Bool :=
  !hasDuplicate actual && actual.mergeSort == expected.mergeSort

private def requireMembers (context : String) (json : Json)
    (expected : List String) : Except String Unit := do
  let actual ← objectNames context json
  if !sameInventory actual expected then
    throw s!"{context} has unknown, missing, or duplicate members"

private def parseField (json : Json) : Except String FieldSpec := do
  pure {
    id := ← member json "id"
    groups := ← member json "groups"
    name := ← member json "name" }

private def parseExpr : Nat → Json → Except String ExprSpec
  | 0, _ => throw "String-computation expression exceeds maximum depth"
  | fuel + 1, json => do
      let tag : String ← member json "tag"
      match tag with
      | "field" => pure (.field (← member json "fieldId"))
      | "literal" => pure (.literal (← member json "value"))
      | "concat" =>
          pure (.concat
            (← parseExpr fuel (← json.getObjVal? "left"))
            (← parseExpr fuel (← json.getObjVal? "right")))
      | other => throw s!"unsupported String-computation expression '{other}'"

private def parseModel (json : Json) : Except String ModelSpec := do
  let fields : List Json ← member json "fields"
  pure {
    id := ← member json "id"
    modelRef := ← member json "modelRef"
    modelSha256 := ← member json "modelSha256"
    declaringGroup := ← member json "declaringGroup"
    fields := ← fields.mapM parseField
    computationName := ← member json "computationName"
    targetFieldId := ← member json "targetFieldId"
    targetRelPath := ← member json "targetRelPath"
    targetPointer := ← member json "targetPointer"
    expression := ← parseExpr 64 (← json.getObjVal? "expression") }

private def parseCell (json : Json) : Except String CellSpec := do
  let stateJson ← json.getObjVal? "state"
  let tag : String ← member stateJson "tag"
  let state ← match tag with
    | "empty" => pure .empty
    | "string" => pure (.string (← member stateJson "value"))
    | other => throw s!"unsupported String-computation cell state '{other}'"
  pure { fieldId := ← member json "fieldId", state }

private def parseTarget (json : Json) : Except String TargetStateSpec := do
  let tag : String ← member json "tag"
  match tag with
  | "empty" => pure .empty
  | "string" => pure (.string (← member json "value"))
  | other => throw s!"unsupported prior String target state '{other}'"

private def parseCase (json : Json) : Except String CaseSpec := do
  let cells : List Json ← member json "cells"
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    caseSha256 := ← member json "caseSha256"
    modelId := ← member json "modelId"
    cells := ← cells.mapM parseCell
    priorTarget := ← parseTarget (← json.getObjVal? "priorTarget")
    hasContent := ← member json "hasContent" }

private def validateFieldShape (index : Nat) (json : Json) : Except String Unit :=
  requireMembers s!"String-computation projection model field {index}" json
    ["id", "groups", "name"]

private def validateExpressionShape : Nat → String → Json → Except String Unit
  | 0, context, _ => throw s!"{context} exceeds the projection-shape depth limit"
  | fuel + 1, context, json => do
      let tag : String ← member json "tag"
      match tag with
      | "field" => requireMembers context json ["tag", "fieldId"]
      | "literal" => requireMembers context json ["tag", "value"]
      | "concat" => do
          requireMembers context json ["tag", "left", "right"]
          validateExpressionShape fuel (context ++ ".left") (← json.getObjVal? "left")
          validateExpressionShape fuel (context ++ ".right") (← json.getObjVal? "right")
      | other => throw s!"{context} has unsupported expression tag '{other}'"

private def validateStateShape (context : String) (json : Json) : Except String Unit := do
  let tag : String ← member json "tag"
  match tag with
  | "empty" => requireMembers context json ["tag"]
  | "string" => requireMembers context json ["tag", "value"]
  | other => throw s!"{context} has unsupported state tag '{other}'"

private def validateModelShape (index : Nat) (json : Json) : Except String Unit := do
  let context := s!"String-computation projection model {index}"
  requireMembers context json [
    "id", "modelRef", "modelSha256", "declaringGroup", "fields", "computationName",
    "targetFieldId", "targetRelPath", "targetPointer", "expression"]
  let fields : List Json ← member json "fields"
  for entry in fields.zipIdx do
    validateFieldShape entry.2 entry.1
  validateExpressionShape 64 (context ++ ".expression") (← json.getObjVal? "expression")

private def validateCaseShape (index : Nat) (json : Json) : Except String Unit := do
  let context := s!"String-computation projection case {index}"
  requireMembers context json [
    "id", "caseRef", "caseSha256", "modelId", "cells", "priorTarget", "hasContent"]
  let cells : List Json ← member json "cells"
  for entry in cells.zipIdx do
    let cellContext := s!"{context}.cells[{entry.2}]"
    requireMembers cellContext entry.1 ["fieldId", "state"]
    validateStateShape (cellContext ++ ".state") (← entry.1.getObjVal? "state")
  validateStateShape (context ++ ".priorTarget") (← json.getObjVal? "priorTarget")

private def validateShape (json : Json) : Except String Unit := do
  requireMembers "String-computation projection" json [
    "schemaVersion", "kernelVersion", "captureRef", "captureSha256", "sourceRevision",
    "models", "cases"]
  let models : List Json ← member json "models"
  for entry in models.zipIdx do
    validateModelShape entry.2 entry.1
  let cases : List Json ← member json "cases"
  for entry in cases.zipIdx do
    validateCaseShape entry.2 entry.1

def Bundle.fromJson (json : Json) : Except String Bundle := do
  validateShape json
  let models : List Json ← member json "models"
  let cases : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    captureRef := ← member json "captureRef"
    captureSha256 := ← member json "captureSha256"
    sourceRevision := ← member json "sourceRevision"
    models := ← models.mapM parseModel
    cases := ← cases.mapM parseCase }

private def emptyStateWithExtra : Json :=
  Json.mkObj [("tag", toJson "empty"), ("extra", toJson true)]

private def fieldExpressionWithExtra : Json :=
  Json.mkObj [("tag", toJson "field"), ("fieldId", toJson 1), ("extra", toJson true)]

example : (validateStateShape "state" emptyStateWithExtra).isOk = false := by native_decide
example : (validateExpressionShape 64 "expression" fieldExpressionWithExtra).isOk = false := by
  native_decide

end A12Kernel.Evidence.StringComputation
