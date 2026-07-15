import Lean.Data.Json

/-! # A12Kernel.Evidence.StringTargetValidationSchema — target-validation evidence transport

The projection contains only replay inputs and retained artifact identities. Expected deltas and exact external application states remain solely in the independently captured case files.
-/

namespace A12Kernel.Evidence.StringTargetValidation

open Lean

inductive OperationSpec where
  | copy
  | padded (before after : String)
  deriving Repr, DecidableEq

inductive LengthPolicySpec where
  | minimum (bound : Nat)
  | maximum (bound : Nat)
  deriving Repr, DecidableEq

structure ModelSpec where
  id : String
  modelRef : String
  modelSha256 : String
  operation : OperationSpec
  policy : LengthPolicySpec
  deriving Repr, DecidableEq

inductive PriorTargetSpec where
  | absent
  | string (value : String)
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  caseSha256 : String
  modelId : String
  source : String
  priorTarget : PriorTargetSpec
  deriving Repr, DecidableEq

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  captureRef : String
  captureSha256 : String
  sourceRevision : String
  targetPointer : String
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

private def parseOperation (json : Json) : Except String OperationSpec := do
  let tag : String ← member json "tag"
  match tag with
  | "copy" => pure .copy
  | "padded" => pure (.padded (← member json "prefix") (← member json "suffix"))
  | other => throw s!"unsupported target-validation operation '{other}'"

private def parsePolicy (json : Json) : Except String LengthPolicySpec := do
  let tag : String ← member json "tag"
  match tag with
  | "minimum" => pure (.minimum (← member json "bound"))
  | "maximum" => pure (.maximum (← member json "bound"))
  | other => throw s!"unsupported target-validation length policy '{other}'"

private def parseModel (json : Json) : Except String ModelSpec := do
  pure {
    id := ← member json "id"
    modelRef := ← member json "modelRef"
    modelSha256 := ← member json "modelSha256"
    operation := ← parseOperation (← json.getObjVal? "operation")
    policy := ← parsePolicy (← json.getObjVal? "policy") }

private def parsePriorTarget (json : Json) : Except String PriorTargetSpec := do
  let tag : String ← member json "tag"
  match tag with
  | "absent" => pure .absent
  | "string" => pure (.string (← member json "value"))
  | other => throw s!"unsupported prior target state '{other}'"

private def parseCase (json : Json) : Except String CaseSpec := do
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    caseSha256 := ← member json "caseSha256"
    modelId := ← member json "modelId"
    source := ← member json "source"
    priorTarget := ← parsePriorTarget (← json.getObjVal? "priorTarget") }

private def validateOperationShape (context : String) (json : Json) : Except String Unit := do
  let tag : String ← member json "tag"
  match tag with
  | "copy" => requireMembers context json ["tag"]
  | "padded" => requireMembers context json ["tag", "prefix", "suffix"]
  | other => throw s!"{context} has unsupported operation tag '{other}'"

private def validatePolicyShape (context : String) (json : Json) : Except String Unit := do
  let tag : String ← member json "tag"
  match tag with
  | "minimum" | "maximum" => requireMembers context json ["tag", "bound"]
  | other => throw s!"{context} has unsupported length-policy tag '{other}'"

private def validatePriorTargetShape (context : String) (json : Json) : Except String Unit := do
  let tag : String ← member json "tag"
  match tag with
  | "absent" => requireMembers context json ["tag"]
  | "string" => requireMembers context json ["tag", "value"]
  | other => throw s!"{context} has unsupported prior-target tag '{other}'"

private def validateModelShape (index : Nat) (json : Json) : Except String Unit := do
  let context := s!"String target-validation projection model {index}"
  requireMembers context json ["id", "modelRef", "modelSha256", "operation", "policy"]
  validateOperationShape (context ++ ".operation") (← json.getObjVal? "operation")
  validatePolicyShape (context ++ ".policy") (← json.getObjVal? "policy")

private def validateCaseShape (index : Nat) (json : Json) : Except String Unit := do
  let context := s!"String target-validation projection case {index}"
  requireMembers context json ["id", "caseRef", "caseSha256", "modelId", "source", "priorTarget"]
  validatePriorTargetShape (context ++ ".priorTarget") (← json.getObjVal? "priorTarget")

private def validateShape (json : Json) : Except String Unit := do
  requireMembers "String target-validation projection" json [
    "schemaVersion", "kernelVersion", "captureRef", "captureSha256", "sourceRevision",
    "targetPointer", "models", "cases"]
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
    targetPointer := ← member json "targetPointer"
    models := ← models.mapM parseModel
    cases := ← cases.mapM parseCase }

private def copyOperationWithExtra : Json :=
  Json.mkObj [("tag", toJson "copy"), ("extra", toJson true)]

private def absentPriorWithValue : Json :=
  Json.mkObj [("tag", toJson "absent"), ("value", toJson "hidden")]

example : (validateOperationShape "operation" copyOperationWithExtra).isOk = false := by
  native_decide

example : (validatePriorTargetShape "prior" absentPriorWithValue).isOk = false := by
  native_decide

end A12Kernel.Evidence.StringTargetValidation
