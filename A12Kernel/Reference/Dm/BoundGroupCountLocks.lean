import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.BoundGroupCountLocks
open Lean A12Kernel

private def model : FlatModel :=
  let field (id : Nat) (name : String) (groupPath : GroupPath) (repeatableScope : List Nat) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope,
      policy := { kind := if id == 1 then .string else .number { scale := 0, signed := true } } }
  { fields := [field 1 "Anchor" ["Form", "Rows"] [10],
      field 2 "N" ["Form", "Rows", "A"] [10], field 3 "M" ["Form", "Rows", "A"] [10],
      field 4 "N" ["Form", "Rows", "B"] [10], field 5 "N" ["Form", "Rows", "Items"] [10, 20]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 }] }

private def row (a m b : String) (items : List String) : Json :=
  Json.mkObj [("Anchor", .str "on"), ("A", Json.mkObj [("N", .str a), ("M", .str m)]),
    ("B", Json.mkObj [("N", .str b)]), ("Items", Json.arr (items.map fun n => Json.mkObj [("N", .str n)]).toArray)]

private def scope (name : String) : ValidationRelevanceScope := .partialSet (
  match name with
  | "root" => [{ path := ["Form"], indices := [.all] }]
  | "row1" => [{ path := ["Form", "Rows"], indices := [.concrete 1, .concrete 1] }]
  | "row2" => [{ path := ["Form", "Rows"], indices := [.concrete 1, .concrete 2] }]
  | name => (match name with
      | "fields" => [["Anchor"], ["A", "N"], ["A", "M"], ["B", "N"], ["Items", "N"]]
      | "partial-A" => [["Anchor"], ["A", "M"], ["B"], ["Items"]]
      | _ => [["Anchor"]]).map fun suffix => {
        path := ["Form", "Rows"] ++ suffix, indices := (List.replicate (2 + suffix.length) .all) })

private def rules : List (String × String) := [
  ("ZERO", "NumberOfFilledGroups(A,B) == 0"), ("ONE", "NumberOfFilledGroups(A,B) == 1"),
  ("TWO", "NumberOfFilledGroups(A,B) == 2"), ("LOW", "NumberOfFilledGroups(A,B) < 2"),
  ("HIGH", "NumberOfFilledGroups(A,B) > 0"), ("MIXONE", "NumberOfFilledGroups(A,Items*) == 1"),
  ("MIXTHREE", "NumberOfFilledGroups(A,Items*) == 3")]

private def run (isPartial : Bool) (a m b : String) (items : List String) (coverage : String)
    (noRows : Bool := false) : Option (List (String × String × String)) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Rows", Json.arr
    (if noRows then #[] else #[row a m b items, row "" "" "3" ["4"]]))])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let results ← rules.mapM fun (code, condition) => do
    let rule ← (checkRule dm .english {
      name := code, group := ["Form", "Rows"], errorCode := code, errorEntityRelPath := "../Anchor", severity := "ERROR",
      condition := "FieldFilled(Anchor) And " ++ condition }).toOption
    let messages ← if isPartial then
      match ← (rule.evalOrdinaryRepeatablePartial document (scope coverage) (some world)).toOption with
      | .skipped => none
      | .evaluated outcomes => pure (outcomes.flatMap fun (_, outcome) => match outcome with
          | .skipped => []
          | .evaluated outcome => outcome.message?.toList)
    else (runRule world document rule).toOption
    pure (messages.map fun message => let observed := observe model message; (code, observed.pointer, observed.messageType))
  pure results.flatten

example : run false "1" "2" "" ["1", ""] "root" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "" ["1", ""] "root" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run false "1" "2" "" ["1", ""] "row1" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "" ["1", ""] "row1" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run false "1" "2" "" ["1", ""] "row2" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "" ["1", ""] "row2" false = some [("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run false "1" "2" "" ["1", ""] "anchor-only" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "" ["1", ""] "anchor-only" false = some [] := by native_decide
example : run false "1" "2" "" ["1", ""] "fields" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "" ["1", ""] "fields" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run false "1" "2" "" ["1", ""] "partial-A" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "" ["1", ""] "partial-A" false = some [] := by native_decide
example : run false "" "" "" ["1", ""] "root" false = some [("ZERO", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run true "" "" "" ["1", ""] "root" false = some [("ZERO", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run false "bad" "" "" ["1", ""] "root" false = some [("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run true "bad" "" "" ["1", ""] "root" false = some [("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run false "bad" "2" "" ["1", ""] "root" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "bad" "2" "" ["1", ""] "root" false = some [("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run false "bad" "2" "" ["1", ""] "partial-A" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "bad" "2" "" ["1", ""] "partial-A" false = some [] := by native_decide
example : run false "1" "2" "2" ["1", ""] "root" false = some [("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("TWO", "Form/Rows/Anchor", "VALUE_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run true "1" "2" "2" ["1", ""] "root" false = some [("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("TWO", "Form/Rows/Anchor", "VALUE_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("MIXTHREE", "Form/Rows/Anchor", "VALUE_ERROR")] := by native_decide
example : run false "1" "2" "" [] "root" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run true "1" "2" "" [] "root" false = some [("ONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("ONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows/Anchor", "OMISSION_ERROR"), ("LOW", "Form/Rows[2]/Anchor", "OMISSION_ERROR"), ("HIGH", "Form/Rows/Anchor", "VALUE_ERROR"), ("HIGH", "Form/Rows[2]/Anchor", "VALUE_ERROR"), ("MIXONE", "Form/Rows/Anchor", "OMISSION_ERROR"), ("MIXONE", "Form/Rows[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : run false "1" "2" "" ["1", ""] "root" true = some [] := by native_decide
example : run true "1" "2" "" ["1", ""] "root" true = some [] := by native_decide

end A12Kernel.Dm.BoundGroupCountLocks
