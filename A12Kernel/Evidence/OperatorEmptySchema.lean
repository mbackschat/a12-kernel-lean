import Lean.Data.Json

/-! # A12Kernel.Evidence.OperatorEmptySchema — operator-sensitive empty-value transport

This closed projection carries two retained models, their six runtime cases, and only the four condition forms exercised by the paired String/Length and directional Number capture. Expected results remain in the external case artifacts.
-/

namespace A12Kernel.Evidence.OperatorEmpty

open Lean

inductive FieldKindSpec where
  | number (scale : Nat) (signed : Bool)
  | string
  deriving Repr, DecidableEq

structure FieldSpec where
  id : Nat
  groups : List String
  name : String
  kind : FieldKindSpec
  deriving Repr, DecidableEq

inductive ConditionSpec where
  | numberNotEqual (fieldId : Nat) (expected : Int)
  | stringEqual (fieldId : Nat) (expected : String)
  | stringLengthLess (fieldId : Nat) (expected : Int)
  | stringLengthGreaterEqual (fieldId : Nat) (expected : Int)
  deriving Repr, DecidableEq

structure RuleSpec where
  name : String
  code : String
  errorFieldId : Nat
  errorPointer : String
  condition : ConditionSpec
  deriving Repr, DecidableEq

structure ModelSpec where
  id : String
  modelRef : String
  modelSha256 : String
  declaringGroup : List String
  fields : List FieldSpec
  rules : List RuleSpec
  deriving Repr, DecidableEq

inductive CellStateSpec where
  | empty
  | number (value : Int)
  | string (value : String)
  deriving Repr, DecidableEq

structure CellSpec where
  fieldId : Nat
  state : CellStateSpec
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  caseSha256 : String
  modelId : String
  cells : List CellSpec
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

private def parseFieldKind (json : Json) : Except String FieldKindSpec := do
  let tag : String ← member json "tag"
  match tag with
  | "number" => pure (.number (← member json "scale") (← member json "signed"))
  | "string" => pure .string
  | other => throw s!"unsupported operator-empty field kind '{other}'"

private def parseField (json : Json) : Except String FieldSpec := do
  pure {
    id := ← member json "id"
    groups := ← member json "groups"
    name := ← member json "name"
    kind := ← parseFieldKind (← json.getObjVal? "kind") }

private def parseCondition (json : Json) : Except String ConditionSpec := do
  let tag : String ← member json "tag"
  match tag with
  | "numberNotEqual" => pure (.numberNotEqual (← member json "fieldId") (← member json "expected"))
  | "stringEqual" => pure (.stringEqual (← member json "fieldId") (← member json "expected"))
  | "stringLengthLess" => pure (.stringLengthLess (← member json "fieldId") (← member json "expected"))
  | "stringLengthGreaterEqual" =>
      pure (.stringLengthGreaterEqual (← member json "fieldId") (← member json "expected"))
  | other => throw s!"unsupported operator-empty condition '{other}'"

private def parseRule (json : Json) : Except String RuleSpec := do
  pure {
    name := ← member json "name"
    code := ← member json "code"
    errorFieldId := ← member json "errorFieldId"
    errorPointer := ← member json "errorPointer"
    condition := ← parseCondition (← json.getObjVal? "condition") }

private def parseModel (json : Json) : Except String ModelSpec := do
  let fields : List Json ← member json "fields"
  let rules : List Json ← member json "rules"
  pure {
    id := ← member json "id"
    modelRef := ← member json "modelRef"
    modelSha256 := ← member json "modelSha256"
    declaringGroup := ← member json "declaringGroup"
    fields := ← fields.mapM parseField
    rules := ← rules.mapM parseRule }

private def parseCell (json : Json) : Except String CellSpec := do
  let stateJson ← json.getObjVal? "state"
  let tag : String ← member stateJson "tag"
  let state ← match tag with
    | "empty" => pure .empty
    | "number" => pure (.number (← member stateJson "value"))
    | "string" => pure (.string (← member stateJson "value"))
    | other => throw s!"unsupported operator-empty cell state '{other}'"
  pure { fieldId := ← member json "fieldId", state }

private def parseCase (json : Json) : Except String CaseSpec := do
  let cells : List Json ← member json "cells"
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    caseSha256 := ← member json "caseSha256"
    modelId := ← member json "modelId"
    cells := ← cells.mapM parseCell
    hasContent := ← member json "hasContent" }

def Bundle.fromJson (json : Json) : Except String Bundle := do
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

end A12Kernel.Evidence.OperatorEmpty
