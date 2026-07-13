import Lean.Data.Json

/-! # A12Kernel.Evidence.Schema — portable evidence projection

This transport is deliberately narrower than a12-dmkits' full conformance schema. It
starts at the same structured, parser-independent boundary as the current Lean capsule.
The external case remains the source of the observable kernel signatures; this schema
contains only the typed input needed to replay that observation through Lean.
-/

namespace A12Kernel.Evidence

open Lean

inductive FieldKindSpec where
  | number (scale : Nat) (signed : Bool)
  | boolean
  | confirm
  deriving Repr, DecidableEq

structure FieldSpec where
  id : Nat
  groups : List String
  name : String
  kind : FieldKindSpec
  deriving Repr, DecidableEq

inductive PathBaseSpec where
  | absolute
  | relative (parents : Nat)
  deriving Repr, DecidableEq

structure PathSpec where
  base : PathBaseSpec
  groups : List String
  field : String
  deriving Repr, DecidableEq

inductive LiteralSpec where
  | number (value : Int)
  | boolean (value : Bool)
  deriving Repr, DecidableEq

inductive ConditionSpec where
  | compare (comparison : String) (path : PathSpec) (literal : LiteralSpec)
  | fieldNotFilled (path : PathSpec)
  | and (left right : ConditionSpec)
  | or (left right : ConditionSpec)
  deriving Repr, DecidableEq

inductive CellStateSpec where
  | empty
  | number (value : Int)
  | boolean (value : Bool)
  | confirm (value : Bool)
  | rejected
  deriving Repr, DecidableEq

structure CellSpec where
  fieldId : Nat
  state : CellStateSpec
  deriving Repr, DecidableEq

inductive OperationSpec where
  | flat (declaringGroup : List String) (condition : ConditionSpec) (hasContent : Bool)
  | absoluteRequired (targetFieldId : Nat)
  | resolve (declaringGroup : List String) (path : PathSpec)
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  focusCode : String
  focusPointer : String
  fieldRefByShortNameAllowed : Bool
  fields : List FieldSpec
  cells : List CellSpec
  operation : OperationSpec
  deriving Repr, DecidableEq

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  cases : List CaseSpec
  deriving Repr, DecidableEq

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def memberD [FromJson α] (json : Json) (name : String) (fallback : α) :
    Except String α :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure fallback

private def parseField (json : Json) : Except String FieldSpec := do
  let kind : String ← member json "kind"
  let fieldKind ← match kind with
    | "number" => pure (.number (← member json "scale") (← member json "signed"))
    | "boolean" => pure .boolean
    | "confirm" => pure .confirm
    | other => throw s!"unsupported field kind '{other}'"
  pure {
    id := ← member json "id"
    groups := ← member json "groups"
    name := ← member json "name"
    kind := fieldKind }

private def parsePath (json : Json) : Except String PathSpec := do
  let baseName : String ← member json "base"
  let base ← match baseName with
    | "absolute" => pure .absolute
    | "relative" => pure (.relative (← member json "parents"))
    | other => throw s!"unsupported path base '{other}'"
  pure {
    base
    groups := ← member json "groups"
    field := ← member json "field" }

private def parseLiteral (json : Json) : Except String LiteralSpec := do
  let kind : String ← member json "kind"
  match kind with
  | "number" => pure (.number (← member json "number"))
  | "boolean" => pure (.boolean (← member json "boolean"))
  | other => throw s!"unsupported literal kind '{other}'"

private def parseCondition : Nat → Json → Except String ConditionSpec
  | 0, _ => throw "condition nesting exceeds evidence-v1 limit"
  | fuel + 1, json => do
      let kind : String ← member json "kind"
      match kind with
      | "compare" => pure (.compare (← member json "comparison")
          (← parsePath (← json.getObjVal? "path"))
          (← parseLiteral (← json.getObjVal? "literal")))
      | "fieldNotFilled" => pure (.fieldNotFilled (← parsePath (← json.getObjVal? "path")))
      | "and" => pure (.and
          (← parseCondition fuel (← json.getObjVal? "left"))
          (← parseCondition fuel (← json.getObjVal? "right")))
      | "or" => pure (.or
          (← parseCondition fuel (← json.getObjVal? "left"))
          (← parseCondition fuel (← json.getObjVal? "right")))
      | other => throw s!"unsupported condition kind '{other}'"

private def parseCell (json : Json) : Except String CellSpec := do
  let stateName : String ← member json "state"
  let state ← match stateName with
    | "empty" => pure .empty
    | "number" => pure (.number (← member json "number"))
    | "boolean" => pure (.boolean (← member json "boolean"))
    | "confirm" => pure (.confirm (← member json "confirm"))
    | "rejected" => pure .rejected
    | other => throw s!"unsupported cell state '{other}'"
  pure { fieldId := ← member json "fieldId", state }

private def parseCase (json : Json) : Except String CaseSpec := do
  let operationName : String ← member json "operation"
  let operation ← match operationName with
    | "flat" => pure (.flat
        (← member json "declaringGroup")
        (← parseCondition 64 (← json.getObjVal? "condition"))
        (← member json "hasContent"))
    | "absoluteRequired" => pure (.absoluteRequired (← member json "targetFieldId"))
    | "resolve" => pure (.resolve
        (← member json "declaringGroup")
        (← parsePath (← json.getObjVal? "path")))
    | other => throw s!"unsupported evidence operation '{other}'"
  let fieldJson : List Json ← member json "fields"
  let cellJson : List Json ← member json "cells"
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    focusCode := ← member json "focusCode"
    focusPointer := ← member json "focusPointer"
    fieldRefByShortNameAllowed := ← memberD json "fieldRefByShortNameAllowed" true
    fields := ← fieldJson.mapM parseField
    cells := ← cellJson.mapM parseCell
    operation }

def Bundle.fromJson (json : Json) : Except String Bundle := do
  let caseJson : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    cases := ← caseJson.mapM parseCase }

end A12Kernel.Evidence
