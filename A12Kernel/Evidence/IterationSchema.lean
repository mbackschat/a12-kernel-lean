import Lean.Data.Json

/-! # A12Kernel.Evidence.IterationSchema — single-level iteration evidence transport

This closed projection is separate from the flat evidence schema. It carries only the
typed input required by the first iteration capsule; the expected result remains solely
in the retained external case referenced by `caseRef`.
-/

namespace A12Kernel.Evidence.Iteration

open Lean

structure NumberFieldSpec where
  id : Nat
  scale : Nat
  signed : Bool
  deriving Repr, DecidableEq

inductive NumberCellStateSpec where
  | empty
  | number (value : Int)
  | rejected
  deriving Repr, DecidableEq

structure NumberCellSpec where
  rowId : Nat
  fieldId : Nat
  state : NumberCellStateSpec
  deriving Repr, DecidableEq

/-- The only admitted filter: row-local equality between one numeric field and an
    integer literal. The absence of this object denotes an unfiltered star. -/
structure HavingSpec where
  fieldId : Nat
  equals : Int
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  focusCode : String
  focusPointer : String
  groupId : Nat
  rowIds : List Nat
  fields : List NumberFieldSpec
  cells : List NumberCellSpec
  having : Option HavingSpec
  valueFieldId : Nat
  equals : Int
  deriving Repr, DecidableEq

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  cases : List CaseSpec
  deriving Repr, DecidableEq

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def parseField (json : Json) : Except String NumberFieldSpec := do
  pure {
    id := ← member json "id"
    scale := ← member json "scale"
    signed := ← member json "signed" }

private def parseCell (json : Json) : Except String NumberCellSpec := do
  let stateName : String ← member json "state"
  let state ← match stateName with
    | "empty" => pure .empty
    | "number" => pure (.number (← member json "number"))
    | "rejected" => pure .rejected
    | other => throw s!"unsupported iteration cell state '{other}'"
  pure {
    rowId := ← member json "rowId"
    fieldId := ← member json "fieldId"
    state }

private def parseHaving (json : Json) : Except String HavingSpec := do
  pure {
    fieldId := ← member json "fieldId"
    equals := ← member json "equals" }

private def optionalHaving (json : Json) : Except String (Option HavingSpec) :=
  match json.getObjVal? "having" with
  | .error _ => pure none
  | .ok .null => pure none
  | .ok value => some <$> parseHaving value

private def parseCase (json : Json) : Except String CaseSpec := do
  let operation : String ← member json "operation"
  if operation != "sumEquals" then
    throw s!"unsupported iteration evidence operation '{operation}'"
  let fieldJson : List Json ← member json "fields"
  let cellJson : List Json ← member json "cells"
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    focusCode := ← member json "focusCode"
    focusPointer := ← member json "focusPointer"
    groupId := ← member json "groupId"
    rowIds := ← member json "rowIds"
    fields := ← fieldJson.mapM parseField
    cells := ← cellJson.mapM parseCell
    having := ← optionalHaving json
    valueFieldId := ← member json "valueFieldId"
    equals := ← member json "equals" }

def Bundle.fromJson (json : Json) : Except String Bundle := do
  let caseJson : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    cases := ← caseJson.mapM parseCase }

end A12Kernel.Evidence.Iteration
