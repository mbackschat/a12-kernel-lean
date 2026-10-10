import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.NestedFirstFilledLocks
open A12Kernel Lean

private def model : FlatModel :=
  let text (id : FieldId) (name : String) (groupPath : GroupPath) (repeatableScope : List RepeatableLevel) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope, policy := { kind := .string } }
  let roots := ["Anchor", "Head", "Tail", "Bare", "Filtered", "Prefix", "Fallback"].zipIdx |>.map fun (name, i) => text (i + 1) name ["Form"] []
  let parents := ["Local", "Global", "Captured"].zipIdx |>.map fun (name, i) => text (i + 8) name ["Form", "Parents"] [10]
  { fields := roots ++ parents ++ [text 11 "Text" ["Form", "Parents", "Rows"] [10, 20],
      { text 12 "Limit" ["Form", "Parents"] [10] with policy := { kind := .number { scale := 0, signed := true } } },
      { text 13 "Keep" ["Form", "Parents", "Rows"] [10, 20] with policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Parents"], repeatability := some 3 },
      { level := 20, path := ["Form", "Parents", "Rows"], repeatability := some 3 }] }

private def input (parents : List (String × List (String × String))) (head : String := "H")
    (missingFirstRows : Bool := false) : Json :=
  let row (text keep : String) := Json.mkObj [("Text", .str text), ("Keep", .str keep)]
  let parent (limit : String) (rows : List (String × String)) (missing : Bool) := Json.mkObj
    ([("Limit", .str limit), ("Local", .str "99"), ("Global", .str "99"), ("Captured", .str "99")] ++
      if missing then [] else [("Rows", .arr (rows.map fun (text, keep) => row text keep).toArray)])
  Json.mkObj [("Form", Json.mkObj [
    ("Anchor", .str "ON"), ("Head", .str head), ("Tail", .str "T"),
    ("Bare", .str "99"), ("Filtered", .str "99"), ("Prefix", .str "99"), ("Fallback", .str "99"),
    ("Parents", .arr (parents.zipIdx.map fun ((limit, rows), i) => parent limit rows (missingFirstRows && i == 0)).toArray)])]

private def localOperation :=
  "FirstFilledValue(/Form/Parents/Rows*/Text Having [/Form/Parents/Rows/Keep] > 0)"
private def operations : List (String × String) := [
  ("Bare", "FirstFilledValue(/Form/Parents*/Rows*/Text)"),
  ("Filtered", "FirstFilledValue(/Form/Parents*/Rows*/Text Having [/Form/Parents/Rows/Keep] > 0)"),
  ("Prefix", "FirstFilledValue(/Form/Head,/Form/Parents*/Rows*/Text Having [/Form/Parents/Rows/Keep] > 0)"),
  ("Fallback", "FirstFilledValue(/Form/Parents*/Rows*/Text Having [/Form/Parents/Rows/Keep] > 0,/Form/Tail)"),
  ("Parents/Local", localOperation),
  ("Parents/Global", "FirstFilledValue(/Form/Parents*/Rows*/Text Having [/Form/Parents/Rows/Keep] > 0)"),
  ("Parents/Captured", "FirstFilledValue(/Form/Parents*/Rows*/Text Having [/Form/Parents/Rows/Keep] <= [$/Form/Parents/Limit])")]

private def run (parents : List (String × List (String × String))) (head : String := "H")
    (missingFirstRows : Bool := false) (selected : List (String × String) := operations) :
    Option (List (String × String)) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let raw ← (readDocument dm (input parents head missingFirstRows)).toOption
  if !raw.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let steps ← selected.mapM fun (target, operation) => do
    let (_, step) ← (lowerComputation model .english {
      name := target, group := ["Form"], targetRelPath := "../" ++ target
      commonPrecondition := none, alternatives := [{ precondition := none, operation }]
      errorCodesToSuppress := [] }).toOption
    pure step
  pure (((← (runComputations world prepared checked steps).toOption).map fun outcome => (outcome.pointer, outcome.outcome)).mergeSort
    (fun left right => decide (left.1 ≤ right.1)))

example : run [("1", [("", "1"), ("B", "1")]), ("1", [("A", "1")])]
    (selected := [("Parents/Local", localOperation)]) =
      some [("Form/Parents/Local", "value B"), ("Form/Parents[2]/Local", "value A")] := by native_decide

example : run [("1", [("", "1"), ("B", "1")]), ("1", [("A", "1")])] = some [
    ("Form/Bare", "value B"), ("Form/Fallback", "value B"), ("Form/Filtered", "value B"),
    ("Form/Parents/Captured", "value B"), ("Form/Parents/Global", "value B"), ("Form/Parents/Local", "value B"),
    ("Form/Parents[2]/Captured", "value B"), ("Form/Parents[2]/Global", "value B"), ("Form/Parents[2]/Local", "value A"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("A", "1")]), ("1", [("B", "1")])] = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "value A"), ("Form/Filtered", "value A"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "value A"), ("Form/Parents/Local", "value A"),
    ("Form/Parents[2]/Captured", "value A"), ("Form/Parents[2]/Global", "value A"), ("Form/Parents[2]/Local", "value B"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [] = some [
    ("Form/Bare", "cleared"), ("Form/Fallback", "value T"), ("Form/Filtered", "cleared"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", []), ("1", [("A", "1")])] = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "value A"), ("Form/Filtered", "value A"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "value A"), ("Form/Parents/Local", "cleared"),
    ("Form/Parents[2]/Captured", "value A"), ("Form/Parents[2]/Global", "value A"), ("Form/Parents[2]/Local", "value A"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("", "1")]), ("1", [("", "1")])] = some [
    ("Form/Bare", "cleared"), ("Form/Fallback", "value T"), ("Form/Filtered", "cleared"),
    ("Form/Parents/Captured", "cleared"), ("Form/Parents/Global", "cleared"), ("Form/Parents/Local", "cleared"),
    ("Form/Parents[2]/Captured", "cleared"), ("Form/Parents[2]/Global", "cleared"), ("Form/Parents[2]/Local", "cleared"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("B", "0")]), ("1", [("A", "1")])] = some [
    ("Form/Bare", "value B"), ("Form/Fallback", "value A"), ("Form/Filtered", "value A"),
    ("Form/Parents/Captured", "value B"), ("Form/Parents/Global", "value A"), ("Form/Parents/Local", "cleared"),
    ("Form/Parents[2]/Captured", "value B"), ("Form/Parents[2]/Global", "value A"), ("Form/Parents[2]/Local", "value A"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("A", "0")]), ("1", [("B", "0")])] = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "value T"), ("Form/Filtered", "cleared"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "cleared"), ("Form/Parents/Local", "cleared"),
    ("Form/Parents[2]/Captured", "value A"), ("Form/Parents[2]/Global", "cleared"), ("Form/Parents[2]/Local", "cleared"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("A", "bad")]), ("1", [("B", "1")])] = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "cleared"), ("Form/Filtered", "cleared"),
    ("Form/Parents/Captured", "cleared"), ("Form/Parents/Global", "cleared"), ("Form/Parents/Local", "cleared"),
    ("Form/Parents[2]/Captured", "cleared"), ("Form/Parents[2]/Global", "cleared"), ("Form/Parents[2]/Local", "value B"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("A", "1")]), ("1", [("B", "1"), ("C", "bad")])] = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "value A"), ("Form/Filtered", "value A"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "value A"), ("Form/Parents/Local", "value A"),
    ("Form/Parents[2]/Captured", "value A"), ("Form/Parents[2]/Global", "value A"), ("Form/Parents[2]/Local", "cleared"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("A", "1")]), ("1", [("B", "0"), ("C", "bad")])] = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "cleared"), ("Form/Filtered", "cleared"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "cleared"), ("Form/Parents/Local", "value A"),
    ("Form/Parents[2]/Captured", "value A"), ("Form/Parents[2]/Global", "cleared"), ("Form/Parents[2]/Local", "cleared"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("B", "2")]), ("2", [("A", "1")])] = some [
    ("Form/Bare", "value B"), ("Form/Fallback", "value B"), ("Form/Filtered", "value B"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "value B"), ("Form/Parents/Local", "value B"),
    ("Form/Parents[2]/Captured", "value B"), ("Form/Parents[2]/Global", "value B"), ("Form/Parents[2]/Local", "value A"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", []), ("1", [("A", "1")])] (missingFirstRows := true) = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "value A"), ("Form/Filtered", "value A"),
    ("Form/Parents/Captured", "value A"), ("Form/Parents/Global", "value A"), ("Form/Parents/Local", "cleared"),
    ("Form/Parents[2]/Captured", "value A"), ("Form/Parents[2]/Global", "value A"), ("Form/Parents[2]/Local", "value A"),
    ("Form/Prefix", "value H")] := by native_decide

example : run [("1", [("A", "bad")])] (head := "") = some [
    ("Form/Bare", "value A"), ("Form/Fallback", "cleared"), ("Form/Filtered", "cleared"),
    ("Form/Parents/Captured", "cleared"), ("Form/Parents/Global", "cleared"), ("Form/Parents/Local", "cleared"),
    ("Form/Prefix", "cleared")] := by native_decide

end A12Kernel.Dm.NestedFirstFilledLocks
