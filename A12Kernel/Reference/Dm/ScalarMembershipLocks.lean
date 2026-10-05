import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ScalarMembershipLocks
open A12Kernel Lean

private def model (kind : FieldKind) : FlatModel := {
  fields := ([1, 2, 3] : List Nat).map fun id => {
    id, groupPath := ["Form"], name := if id == 1 then "A" else if id == 2 then "B" else "C"
    policy := { kind }
    enumeration := if kind == .enumeration then some {
      storedTokens := ["1", "2"], categories := [{ name := "Swap", tokens := ["2", "1"] }] } else none } }

private def run (kind : FieldKind) (condition : String) (member : String := "1") : Option Bool := do
  let model := model kind
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let checked ← (checkRule dm .english {
    group := ["Form"], name := "R", errorCode := "R", errorEntityRelPath := "../A"
    condition, severity := "ERROR" }).toOption
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("A", Json.str "1"), ("B", Json.str member), ("C", Json.str "2")])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure (!(← (runRule world document checked).toOption).isEmpty)

private def kinds : List FieldKind := [.number { scale := 0, signed := true }, .string, .enumeration]

example : kinds.map (fun kind =>
    [run kind "FieldValueIncludedInValueList(A, [B])",
     run kind "FieldValueNotIncludedInValueList(A, [B])",
     run kind "FieldValueIncludedInValueList(A, [B])" "2",
     run kind "FieldValueNotIncludedInValueList(A, [B])" "2",
     run kind "FieldValueIncludedInValueList(A, [B], [C])" "2"]) =
    List.replicate 3 [some true, some false, some false, some true, some false] := by native_decide

example : kinds.all (fun kind =>
    ["FieldValueIncludedInValueList(A, B)", "FieldValueNotIncludedInValueList(A, B)",
     "FieldValueIncludedInValueList([A], [B])", "FieldValueIncludedInValueList(A, [B], C)"].all
      (fun expression => (run kind expression).isNone)) = true := by native_decide

example : run .enumeration "FieldValueIncludedInValueList(A, [B -> Swap])" = some false ∧
    run .enumeration "FieldValueNotIncludedInValueList(A -> Swap, [B])" = some true ∧
    run .enumeration "FieldValueIncludedInValueList(A -> Swap, [B -> Swap])" = some true ∧
    run .enumeration "FieldValueIncludedInValueList(A, B -> Swap)" = none := by native_decide

example : kinds.all (fun kind =>
    run kind "AtLeastOneFieldValueIncludedInValueList(A In B)" == some true &&
    (run kind "AtLeastOneFieldValueIncludedInValueList(A In [B])").isNone) = true ∧
    run .string "FieldValueIncludedInValueList(A, \"1\")" = some true ∧
    run (.number { scale := 0, signed := true }) "FieldValueNotIncludedInValueList(A, 2)" = some true ∧
    run .enumeration "FieldValueIncludedInValueList(A -> Swap, \"2\")" = some true := by native_decide

end A12Kernel.Dm.ScalarMembershipLocks
