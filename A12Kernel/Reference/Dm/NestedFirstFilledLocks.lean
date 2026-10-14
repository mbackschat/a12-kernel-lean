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
      { text 13 "Keep" ["Form", "Parents", "Rows"] [10, 20] with policy := { kind := .number { scale := 0, signed := true } } },
      { text 14 "Flag" ["Form", "Parents", "Rows"] [10, 20] with policy := { kind := .boolean } },
      { text 15 "BareFlag" ["Form"] [] with policy := { kind := .boolean } },
      { text 16 "RowFlag" ["Form", "Parents"] [10] with policy := { kind := .boolean } },
      { text 17 "OwnFlag" ["Form", "Parents"] [10] with policy := { kind := .boolean } },
      { text 18 "Ok" ["Form", "Parents", "Rows"] [10, 20] with policy := { kind := .confirm } },
      { text 19 "OkOut" ["Form"] [] with policy := { kind := .confirm } },
      { text 20 "Cell" ["Form", "Parents", "Rows", "Cells"] [10, 20, 30] with
          policy := { kind := .number { scale := 0, signed := true } } },
      { text 21 "NumOut" ["Form"] [] with policy := { kind := .number { scale := 0, signed := true } } },
      { text 22 "RowNum" ["Form", "Parents"] [10] with policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Parents"], repeatability := some 3 },
      { level := 20, path := ["Form", "Parents", "Rows"], repeatability := some 3 },
      { level := 30, path := ["Form", "Parents", "Rows", "Cells"], repeatability := some 2 }] }

private def input (parents : List (String × List (String × String))) (head : String := "H")
    (missingFirstRows : Bool := false) : Json :=
  let row (text keep : String) := Json.mkObj ([("Text", .str text), ("Keep", .str keep)] ++
    if text.isEmpty then [] else [("Flag", .str (if keep == "1" then "true" else "false"))])
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
      name := target.replace "/" "_", group := ["Form"], targetRelPath := "../" ++ target
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

private def sameLevelRun (own foreign : List String) : Option (List (String × String)) := do
  let text (id : FieldId) (name : String) (root : String) (level : RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := [root, "Rows"], repeatableScope := [level], policy := { kind := .string } }
  let model : FlatModel := {
    fields := [text 1 "Text" "Form" 10, text 2 "Own" "Form" 10,
      text 3 "Away" "Form" 10, text 4 "Text" "Foreign" 20]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Foreign", "Rows"], repeatability := some 2 }] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (value : String) := Json.mkObj [("Text", .str value), ("Own", .str "SEED"), ("Away", .str "SEED")]
  let raw ← (readDocument dm (Json.mkObj [
    ("Form", Json.mkObj [("Rows", .arr (own.map row).toArray)]),
    ("Foreign", Json.mkObj [("Rows", .arr (foreign.map fun value => Json.mkObj [("Text", .str value)]).toArray)])])).toOption
  if !raw.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let steps ← [("Own", "Form"), ("Away", "Foreign")].mapM fun (target, sourceRoot) => do
    let (_, step) ← (lowerComputation model .english {
      group := ["Form"], name := target, targetRelPath := "../Rows/" ++ target
      commonPrecondition := none
      alternatives := [{ precondition := none, operation := "FirstFilledValue(/" ++ sourceRoot ++ "/Rows*/Text)" }]
      errorCodesToSuppress := [] }).toOption
    pure step
  pure (((← (runComputations world prepared checked steps).toOption).map fun outcome =>
    (outcome.pointer, outcome.outcome)).mergeSort (fun left right => decide (left.1 ≤ right.1)))

example : sameLevelRun ["", "Own"] ["Away", "Later"] = some [
    ("Form/Rows/Away", "value Away"), ("Form/Rows/Own", "value Own"),
    ("Form/Rows[2]/Away", "value Away"), ("Form/Rows[2]/Own", "value Own")] := by native_decide

example : sameLevelRun ["Own", ""] ["", "Away"] = some [
    ("Form/Rows/Away", "value Away"), ("Form/Rows/Own", "value Own"),
    ("Form/Rows[2]/Away", "value Away"), ("Form/Rows[2]/Own", "value Own")] := by native_decide

example : sameLevelRun ["", ""] [] = some [
    ("Form/Rows/Away", "cleared"), ("Form/Rows/Own", "cleared"),
    ("Form/Rows[2]/Away", "cleared"), ("Form/Rows[2]/Own", "cleared")] := by native_decide

/-- A typed source under two stars selects parent-major at a fixed target and at a row target that
restars its own group, and in the target's parent at a row target that leaves it bound; the inner-major
account would answer `true` from the second parent's first row
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-typed-first-filled-nested-stars)). -/
example : run [("1", [("", "1"), ("B", "0")]), ("1", [("A", "1")])] (selected := [
      ("BareFlag", "FirstFilledValue(/Form/Parents*/Rows*/Flag)"),
      ("Parents/RowFlag", "FirstFilledValue(/Form/Parents*/Rows*/Flag)"),
      ("Parents/OwnFlag", "FirstFilledValue(/Form/Parents/Rows*/Flag)")]) = some [
    ("Form/BareFlag", "value false"), ("Form/Parents/OwnFlag", "value false"), ("Form/Parents/RowFlag", "value false"),
    ("Form/Parents[2]/OwnFlag", "value true"), ("Form/Parents[2]/RowFlag", "value false")] := by native_decide

/-- The class the reader assigns a first-filled computation it refuses, or none when admitted. -/
private def refusalClass (target operation : String) : Option String :=
  match lowerComputation model .english {
      name := "Static", group := ["Form"], targetRelPath := "../" ++ target, commonPrecondition := none
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] } with
  | .error refusal => some refusal.detail
  | .ok _ => none

/-- Confirm draws `MVK_NO_BOOLY_ALLOWED` under two stars where Boolean is admitted, and Number is
admitted at a fixed target and from a row under one or two reopened stars: row `CfC` of the
[fixed checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-typed-first-filled-nested-stars)
and the Number rows of the
[row checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-typed-first-filled-row-placements). -/
example : refusalClass "OkOut" "FirstFilledValue(/Form/Parents*/Rows*/Ok)" = some "MVK_NO_BOOLY_ALLOWED" ∧
    refusalClass "BareFlag" "FirstFilledValue(/Form/Parents*/Rows*/Flag)" = none ∧
    refusalClass "NumOut" "FirstFilledValue(/Form/Parents*/Rows*/Keep)" = none ∧
    refusalClass "Parents/RowNum" "FirstFilledValue(/Form/Parents/Rows*/Keep)" = none ∧
    refusalClass "Parents/RowNum" "FirstFilledValue(/Form/Parents/Rows*/Cells*/Cell)" = none := by native_decide

end A12Kernel.Dm.NestedFirstFilledLocks
