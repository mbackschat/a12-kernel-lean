import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.SelectedValueListExtentLocks
open Lean A12Kernel

private def model (number : Bool) : FlatModel :=
  let field (id : Nat) (name : String) (groupPath : GroupPath) (repeatableScope : List Nat) (numeric : Bool := false) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope,
      policy := { kind := if numeric then .number { scale := 0, signed := true } else .string } }
  { fields := [field 1 "Anchor" ["Form"] [], field 2 "Key" ["Form"] [],
      field 3 "Needle" ["Form"] [] number, field 4 "Code" ["Form", "Rows"] [10],
      field 5 "V" ["Form", "Rows", "Items"] [10, 20] number]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 4 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 3 }] }

private def run (number group isPartial : Bool) (key : String) (values : List String)
    (parent : Nat) (covered : List Nat) (wildcard : Bool := false) : Option (List String) := do
  let model := model number
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let items (values : List String) := Json.arr (values.map fun v => Json.mkObj [("V", .str v)]).toArray
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Anchor", .str "on"), ("Key", .str key), ("Needle", .str "100"),
    ("Rows", Json.arr #[Json.mkObj [("Code", .str "A"), ("Items", items ["100"])],
      Json.mkObj [("Code", .str "B"), ("Items", items values)]])])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let scope : ValidationRelevanceScope := .partialSet (
    (["Anchor", "Key", "Needle"].map fun name => { path := ["Form", name], indices := [.all, .all] }) ++
    [{ path := ["Form", "Rows", "Code"], indices := [.all, .all, .all] }] ++
    if wildcard then [{ path := ["Form", "Rows", "Items"], indices := [.all, .all, .all] }]
    else covered.map fun row => { path := ["Form", "Rows", "Items"], indices := [.concrete 1, if parent == 0 then .all else .concrete parent, .concrete row] })
  let operand := (if group then "Rows/Items*" else "Rows/Items*/V") ++ " For Key"
  [true, false].flatMapM fun fieldsSide =>
    ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList", "NotAllFieldValuesIncludedInValueList"].mapM fun operator => do
      let pair := if fieldsSide then operand ++ " In Needle" else "Needle In " ++ operand
      let rule ← (checkRule dm .english {
        name := "CHECK", group := ["Form"], errorCode := "CHECK", errorEntityRelPath := "../Anchor", severity := "ERROR",
        condition := "FieldFilled(Anchor) And " ++ operator ++ "(" ++ pair ++ ")" }).toOption
      let messages ← if isPartial then
        match rule.ordinaryIterationPlan with
        | .once _ =>
            match ← (rule.evalOrdinaryOncePartial document scope (some world)).toOption with
            | .skipped => none
            | .evaluated _ outcome => pure outcome.message?.toList
        | .scalar =>
            match ← (rule.evalAddressedPartial document scope (some world)).toOption with
            | .skipped => none
            | .evaluated outcome => pure outcome.message?.toList
        | .rows _ => none
      else (runRule world document rule).toOption
      pure (String.intercalate "," (messages.map fun message => (observe model message).messageType))

private def allForms (isPartial : Bool) (key : String) (values : List String) (parent : Nat)
    (covered : List Nat) (expected : List String) (wildcard : Bool := false) : Bool :=
  [false, true].all fun number => [false, true].all fun group =>
    run number group isPartial key values parent covered wildcard == some expected

private def omission := "OMISSION_ERROR"

example : allForms true "B" ["5", ""] 2 [1, 2, 3] ["", omission, "VALUE_ERROR", "", omission, omission] = true := by native_decide
example : allForms true "B" ["5", ""] 2 [1, 2] ["", "", "VALUE_ERROR", "", "", ""] = true := by native_decide
example : allForms true "B" ["5", ""] 1 [1, 2, 3] ["", "", "", "", "", ""] = true := by native_decide
example : allForms true "B" [] 2 [1, 2, 3] ["", omission, "", "", omission, omission] = true := by native_decide
example : allForms true "B" [] 2 [1, 2] ["", "", "", "", "", ""] = true := by native_decide
example : allForms true "missing" ["5", ""] 0 [1, 2, 3] ["", omission, "", "", omission, omission] = true := by native_decide
example : allForms true "missing" ["5", ""] 2 [1, 2, 3] ["", "", "", "", "", ""] = true := by native_decide
example : allForms true "missing" ["5", ""] 0 [] ["", omission, "", "", omission, omission] true = true := by native_decide
example : allForms false "missing" ["5", ""] 0 [] ["", omission, "", "", omission, omission] = true := by native_decide
example : allForms false "" ["5", ""] 0 [] ["", omission, "", "", omission, omission] = true := by native_decide

end A12Kernel.Dm.SelectedValueListExtentLocks
