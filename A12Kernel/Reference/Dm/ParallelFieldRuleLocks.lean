import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ParallelFieldRuleLocks
open Lean

private def model (signed : Bool := false)
    (rightKind : FieldKind := .number { scale := 0, signed := true }) : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form", "L"], repeatableScope := [10], policy := { kind := .string } },
    { id := 2, name := "N", groupPath := ["Form", "L"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed } } },
    { id := 3, name := "Key", groupPath := ["Form", "R"], repeatableScope := [20], policy := { kind := .string } },
    { id := 4, name := "N", groupPath := ["Form", "R"], repeatableScope := [20], policy := { kind := rightKind } } ]
  repeatableGroups := [
    { level := 10, path := ["Form", "L"], repeatability := some 3, indexField := some 1 },
    { level := 20, path := ["Form", "R"], repeatability := some 3, indexField := some 3 } ] }

private def dm (candidate : FlatModel := model) : DmModel := {
  flat := candidate, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (condition : String) : DmRule := {
  group := ["Form"], name := "Pair", errorCode := "PAIR", severity := "ERROR",
  errorEntityRelPath := "../L/N", condition }

private def documentJson (left right : List (String × String)) : Json :=
  .mkObj [("Form", .mkObj [
    ("L", .arr (left.map fun (key, number) => Json.mkObj [("Key", .str key), ("N", .str number)]).toArray),
    ("R", .arr (right.map fun (key, number) => Json.mkObj [("Key", .str key), ("N", .str number)]).toArray)])]

private def world : World := { now := { epochMillis := 0 } }

private def run (condition : String) (candidate : FlatModel := model)
    (left : List (String × String) := [("Zulu", "7"), ("Alpha", "3")])
    (right : List (String × String) := [("Alpha", "8"), ("Beta", "2")]) :
    Option (List (String × String)) := do
  let input ← (readDocument (dm candidate) (documentJson left right)).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let plan ← (checkValidationRule (dm candidate) .english (rule condition)).toOption
  let messages ← (runValidationRule world checked plan).toOption
  pure (messages.map fun message =>
    let observed := observe candidate message
    (observed.pointer, observed.messageType))

private def admitted (condition : String) (candidate : FlatModel := model) : Bool :=
  (checkParallelRule (dm candidate) .english (rule condition)).isOk

example : (model).validate.isOk = true ∧ (model true).validate.isOk = true := by native_decide

example : run "[L/N] > [R/N]" = some [("Form/L/N", "OMISSION_ERROR")] ∧
    run "[L/N] < [R/N]" = some [("Form/L[2]/N", "VALUE_ERROR"), ("/Form[1]/L[-5]/N", "OMISSION_ERROR")] ∧
    run "[R/N] > [L/N]" = run "[L/N] < [R/N]" := by native_decide

example : run "FieldsNotCollectivelyFilled(L/N, R/N)" =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR"), ("Form/L/N", "OMISSION_ERROR")] ∧
    run "FieldsNotCollectivelyFilled(R/N, L/N)" = run "FieldsNotCollectivelyFilled(L/N, R/N)" := by native_decide

example : run "[L/N] > [R/N]" model [] [("Beta", "-2")] =
    some [("/Form[1]/L[-5]/N", "VALUE_ERROR")] ∧
    run "[L/N] > [R/N]" (model true) [] [("Beta", "-2")] =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR")] := by native_decide

example : run "FieldsNotCollectivelyFilled(L/N, R/N)" model
    [("Zulu", "7"), ("Alpha", "3")] [("Alpha", "8"), ("Beta", "2"), ("", "4")] =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR")] := by native_decide

example : run "FieldFilled(L/N) And FieldFilled(R/N)" =
    some [("Form/L[2]/N", "VALUE_ERROR")] := by native_decide

example : ["==", "!=", "<", "<=", ">", ">="].all
    (fun op => admitted ("[L/N] " ++ op ++ " [R/N]")) = true ∧
    ["AllFieldsFilled", "AtLeastOneFieldFilled", "MoreThanOneFieldFilled", "FieldsNotCollectivelyFilled"].all
      (fun op => admitted (op ++ "(L/N, R/N)")) = true := by native_decide

example : ["NoFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled"].all
    (fun op => !admitted (op ++ "(L/N, R/N)") &&
      admitted ("FieldFilled(L/N) And " ++ op ++ "(L/N, R/N)") &&
      !admitted ("FieldFilled(L/N) Or " ++ op ++ "(L/N, R/N)")) = true := by native_decide

example : ["NoFieldFilled", "NotExactlyOneFieldFilled"].all
    (fun op => run ("[L/N] == [R/N] And " ++ op ++ "(L/N, R/N)") model
      [("Zulu", ""), ("Alpha", "")] [("Alpha", ""), ("Beta", "")] ==
      some [("Form/L[2]/N", "OMISSION_ERROR"), ("/Form[1]/L[-5]/N", "OMISSION_ERROR"),
        ("Form/L/N", "OMISSION_ERROR")]) = true := by native_decide

example :
    let mixed := model false (.number { scale := 2, signed := true })
    !admitted "[L/N] == [R/N]" mixed && admitted "[L/N] > [R/N]" mixed &&
      admitted "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES) [L/N] == [R/N]" mixed = true := by native_decide

example :
    let textRight := model false .string
    !admitted "[L/N] > [R/N]" textRight &&
      admitted "FieldsNotCollectivelyFilled(L/N, R/N)" textRight = true := by native_decide

example : ["FieldsNotCollectivelyFilled([L/N], R/N)", "[L/N] > R/N",
    "[L/N] > [R*/N]", "[L/N] > [R/N For \"Beta\"]",
    "FieldsNotCollectivelyFilled(L/N, L/N)", "[L/N] > 0",
    "@SuppressWarning(MVK_NO_NUMBER) [L/N] > [R/N]"].all
    (fun text => !admitted text) = true := by native_decide

example : !(checkParallelRule dm .english
    { (rule "[L/N] > [R/N]") with
      group := ["Form", "L"]
      errorEntityRelPath := "../N"
      condition := "[N] > [/Form/R/N]" }).isOk := by native_decide

example : run "FieldsNotCollectivelyFilled(L/N, R/N)" model
    [("Zulu", "7"), ("Alpha", "3")] [("Alpha", "8"), ("Beta", "2"), ("Alpha", "4")] =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR")] ∧
    run "[L/N] > [R/N]" model [] [] = some [] := by native_decide

example : run "[L/N] < [R/N]" model [("Alpha", "bad")] [("Alpha", "8")] = some [] ∧
    run "[L/N] < [R/N]" model [("Alpha", "3")] [("Alpha", "8")] =
    some [("Form/L/N", "VALUE_ERROR")] := by native_decide

private def commonOuterModel : FlatModel :=
  let base : FlatModel := model
  { base with
    fields := base.fields.map fun declaration => { declaration with repeatableScope := 99 :: declaration.repeatableScope }
    repeatableGroups := { level := 99, path := ["Form"], repeatability := some 2 } :: base.repeatableGroups }

example : commonOuterModel.validate.isOk = true ∧
    admitted "[L/N] > [R/N]" = true ∧
    admitted "[L/N] > [R/N]" commonOuterModel = false := by native_decide

example : !(checkParallelRule dm .english
    { (rule "[L/N] > [R/N]") with errorEntityRelPath := "../L/Key" }).isOk := by native_decide

example : renderPointer model { field := 2, coordinates := [.unknown] } = "/Form[1]/L[-5]/N" ∧
    renderPointer model { field := 2, coordinates := [.wildcard] } = "/Form[1]/L[0]/N" ∧
    renderPointer model { field := 2, coordinates := [.concrete 2] } = "Form/L[2]/N" ∧
    renderPointer commonOuterModel { field := 2, coordinates := [.unknown, .concrete 2] } =
      "/Form[-5]/L[2]/N" ∧
    renderPointer commonOuterModel { field := 2, coordinates := [.concrete 2, .unknown] } =
      "/Form[2]/L[-5]/N" := by native_decide

end A12Kernel.Dm.ParallelFieldRuleLocks
