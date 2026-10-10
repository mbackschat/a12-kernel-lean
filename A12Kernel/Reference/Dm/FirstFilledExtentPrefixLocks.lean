import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.FirstFilledExtentPrefixLocks
open Lean A12Kernel

private inductive Profile where
  | text | number | boolean

private def profiles := [Profile.text, .number, .boolean]
private def prototype (profile : Profile) : FlatFieldDecl := {
  id := 0, name := "Value", groupPath := ["Form"],
  policy := { kind := match profile with | .text => .string | .number => .number { scale := 0, signed := true } | .boolean => .boolean } }
private def yes : Profile → String | .text => "A" | .number => "1" | .boolean => "true"
private def no : Profile → String | .text => "B" | .number => "2" | .boolean => "false"
private def literal : Profile → String | .text => "\"A\"" | .number => "1" | .boolean => "True"

private def model (profile : Profile) : FlatModel :=
  let field (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) :=
    { prototype profile with id, name, groupPath := path, repeatableScope := scope }
  { fields := [
      { field 1 "Anchor" ["Form"] [] with policy := { kind := .string } },
      { field 2 "Key" ["Form"] [] with policy := { kind := .string } },
      field 3 "X" ["Form", "Block", "First"] [10], field 4 "Y" ["Form", "Block", "Second"] [11],
      field 5 "Z" ["Form", "Groups", "Rows"] [20, 21],
      { field 6 "Id" ["Form", "Buckets"] [30] with policy := { kind := .string } },
      field 7 "X" ["Form", "Buckets", "Block", "First"] [30, 31],
      field 8 "Y" ["Form", "Buckets", "Block", "Second"] [30, 32],
      field 9 "Z" ["Form", "Buckets", "Inner", "Rows"] [30, 40, 41]]
    repeatableGroups := [
      { level := 10, path := ["Form", "Block", "First"], repeatability := some 3 },
      { level := 11, path := ["Form", "Block", "Second"], repeatability := some 3 },
      { level := 20, path := ["Form", "Groups"], repeatability := some 3 },
      { level := 21, path := ["Form", "Groups", "Rows"], repeatability := some 3 },
      { level := 30, path := ["Form", "Buckets"], repeatability := some 3, indexField := some 6 },
      { level := 31, path := ["Form", "Buckets", "Block", "First"], repeatability := some 3 },
      { level := 32, path := ["Form", "Buckets", "Block", "Second"], repeatability := some 3 },
      { level := 40, path := ["Form", "Buckets", "Inner"], repeatability := some 3 },
      { level := 41, path := ["Form", "Buckets", "Inner", "Rows"], repeatability := some 3 }] }

private def run (profile : Profile) (first second : Option (List String)) (keys : List String := ["p"]) :
    Option (List (String × String × String)) := do
  let model := model profile
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (name : String) (value : String) := Json.mkObj [(name, .str value)]
  let block := Json.mkObj ((first.toList.map fun vs => ("First", Json.arr (vs.map (row "X")).toArray)) ++
    (second.toList.map fun vs => ("Second", Json.arr (vs.map (row "Y")).toArray)))
  let groups := Json.arr ([first, second].map fun vs => Json.mkObj (vs.toList.map fun values =>
    ("Rows", Json.arr (values.map (row "Z")).toArray))).toArray
  let buckets := Json.arr (keys.map fun key => Json.mkObj [("Id", .str key), ("Block", block), ("Inner", groups)]).toArray
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Anchor", .str "ON"), ("Key", .str "p"), ("Block", block), ("Groups", groups), ("Buckets", buckets)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let sources := [("GROUP", "Block"), ("STAR_GROUP", "Groups*/Rows*"),
    ("KEY_STAR", "Buckets/Inner*/Rows*/Z For Key"), ("KEY_GROUP", "Buckets/Block For Key"),
    ("KEY_STAR_GROUP", "Buckets/Inner*/Rows* For Key")]
  let results ← sources.mapM fun (code, source) => do
    let rule ← (checkRule dm .english {
      name := code, group := ["Form"], errorCode := code, errorEntityRelPath := "../Anchor", severity := "ERROR",
      condition := "FieldFilled(Anchor) And FirstFilledValue(" ++ source ++ ") == " ++ literal profile }).toOption
    pure ((← (runRule world document rule).toOption).map fun message =>
      let result := observe model message
      (code, result.pointer, result.messageType))
  pure results.flatten

private def expected (messageType : String) (keyed : Bool := true) : List (String × String × String) :=
  ((["GROUP", "STAR_GROUP"] ++ if keyed then ["KEY_STAR", "KEY_GROUP", "KEY_STAR_GROUP"] else []).map
    fun code => (code, "Form/Anchor", messageType))

example : profiles.all (fun p => run p (some []) (some [yes p]) == some (expected "OMISSION_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p none (some [yes p]) == some (expected "OMISSION_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p (some [yes p]) (some []) == some (expected "VALUE_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p (some [yes p]) none == some (expected "VALUE_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p (some [yes p]) (some [no p]) == some (expected "VALUE_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p (some [""]) (some [yes p]) == some (expected "OMISSION_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p (some [yes p, ""]) (some [no p]) == some (expected "VALUE_ERROR")) = true := by native_decide
example : profiles.all (fun p => run p (some []) (some []) == some []) = true := by native_decide
example : profiles.all (fun p => run p (some [no p]) (some [yes p]) == some []) = true := by native_decide
example : profiles.all (fun p => run p (some [yes p]) (some [no p]) ["q"] == some (expected "VALUE_ERROR" false)) = true := by native_decide
example : profiles.all (fun p => run p (some [yes p]) (some [no p]) ["p", "p"] == some (expected "VALUE_ERROR" false)) = true := by native_decide

end A12Kernel.Dm.FirstFilledExtentPrefixLocks
