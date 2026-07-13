import Lean.Data.Json

/-! # A12Kernel.Evidence.CorrelationSchema — captured-outer correlation transport

This closed projection carries only typed inputs for the single-group correlation
capsule. The expected result remains solely in the retained external observation
referenced by `caseRef`.
-/

namespace A12Kernel.Evidence.Correlation

open Lean

structure NumberFieldSpec where
  id : Nat
  path : String
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

inductive OriginSpec where
  | inner
  | outer
  deriving Repr, DecidableEq

inductive ComparisonOpSpec where
  | equal
  | notEqual
  | lessThan
  deriving Repr, DecidableEq

structure NumberRefSpec where
  origin : OriginSpec
  fieldId : Nat
  deriving Repr, DecidableEq

inductive FilterSpec where
  | compareNumbers (op : ComparisonOpSpec) (left right : NumberRefSpec)
  | compareRepetitions (op : ComparisonOpSpec) (left right : OriginSpec)
  | and (left right : FilterSpec)
  deriving Repr, DecidableEq

structure OuterRowSpec where
  rowId : Nat
  pointer : String
  deriving Repr, DecidableEq

structure CaseSpec where
  id : String
  caseRef : String
  focusCode : String
  groupId : Nat
  groupPath : String
  rowIds : List Nat
  fields : List NumberFieldSpec
  cells : List NumberCellSpec
  filter : FilterSpec
  valueFieldId : Nat
  outerRows : List OuterRowSpec
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
    path := ← member json "path"
    scale := ← member json "scale"
    signed := ← member json "signed" }

private def parseCell (json : Json) : Except String NumberCellSpec := do
  let stateName : String ← member json "state"
  let state ← match stateName with
    | "empty" => pure .empty
    | "number" => pure (.number (← member json "number"))
    | "rejected" => pure .rejected
    | other => throw s!"unsupported correlation cell state '{other}'"
  pure {
    rowId := ← member json "rowId"
    fieldId := ← member json "fieldId"
    state }

private def parseOriginName (name : String) : Except String OriginSpec :=
  match name with
  | "inner" => pure .inner
  | "outer" => pure .outer
  | other => throw s!"unsupported correlation reference origin '{other}'"

private def parseOrigin (json : Json) (name : String) : Except String OriginSpec := do
  parseOriginName (← member json name)

private def parseComparison (json : Json) : Except String ComparisonOpSpec := do
  let name : String ← member json "comparison"
  match name with
  | "equal" => pure .equal
  | "notEqual" => pure .notEqual
  | "lessThan" => pure .lessThan
  | other => throw s!"unsupported correlation comparison '{other}'"

private def parseNumberRef (json : Json) : Except String NumberRefSpec := do
  pure {
    origin := ← parseOrigin json "origin"
    fieldId := ← member json "fieldId" }

private def parseFilter : Nat → Json → Except String FilterSpec
  | 0, _ => throw "correlation filter exceeds maximum nesting depth"
  | fuel + 1, json => do
      let kind : String ← member json "kind"
      match kind with
      | "compareNumbers" =>
          pure (.compareNumbers (← parseComparison json)
            (← parseNumberRef (← json.getObjVal? "left"))
            (← parseNumberRef (← json.getObjVal? "right")))
      | "compareRepetitions" =>
          pure (.compareRepetitions (← parseComparison json)
            (← parseOrigin json "left") (← parseOrigin json "right"))
      | "and" =>
          pure (.and (← parseFilter fuel (← json.getObjVal? "left"))
            (← parseFilter fuel (← json.getObjVal? "right")))
      | other => throw s!"unsupported correlation filter node '{other}'"

private def parseOuterRow (json : Json) : Except String OuterRowSpec := do
  pure {
    rowId := ← member json "rowId"
    pointer := ← member json "pointer" }

private def parseCase (json : Json) : Except String CaseSpec := do
  let operation : String ← member json "operation"
  if operation != "guardedAnyFilled" then
    throw s!"unsupported correlation evidence operation '{operation}'"
  let fieldJson : List Json ← member json "fields"
  let cellJson : List Json ← member json "cells"
  let outerRowJson : List Json ← member json "outerRows"
  pure {
    id := ← member json "id"
    caseRef := ← member json "caseRef"
    focusCode := ← member json "focusCode"
    groupId := ← member json "groupId"
    groupPath := ← member json "groupPath"
    rowIds := ← member json "rowIds"
    fields := ← fieldJson.mapM parseField
    cells := ← cellJson.mapM parseCell
    filter := ← parseFilter 64 (← json.getObjVal? "filter")
    valueFieldId := ← member json "valueFieldId"
    outerRows := ← outerRowJson.mapM parseOuterRow }

def Bundle.fromJson (json : Json) : Except String Bundle := do
  let caseJson : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    cases := ← caseJson.mapM parseCase }

end A12Kernel.Evidence.Correlation
