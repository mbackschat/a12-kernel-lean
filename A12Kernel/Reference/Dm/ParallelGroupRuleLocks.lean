import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ParallelGroupRuleLocks
open Lean

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Et", "Rows"], repeatableScope := [9, 10], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 2, name := "Note", groupPath := ["Et", "Rows"], repeatableScope := [9, 10], policy := { kind := .string } },
    { id := 3, name := "Key", groupPath := ["Et", "Side"], repeatableScope := [9, 20], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 4, name := "Val", groupPath := ["Et", "Side"], repeatableScope := [9, 20], policy := { kind := .string } } ]
  repeatableGroups := [
    { level := 9, path := ["Et"], repeatability := some 5 },
    { level := 10, path := ["Et", "Rows"], repeatability := some 5, indexField := some 1 },
    { level := 20, path := ["Et", "Side"], repeatability := some 5, indexField := some 3 } ] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (condition : String) : DmRule := {
  group := ["Et", "Rows"], name := "Parallel", errorCode := "PARALLEL", severity := "ERROR",
  errorEntityRelPath := "../Note", condition }

private def root (left right : List (String × String)) : Json :=
  .mkObj [
    ("Rows", .arr (left.map fun (key, value) => Json.mkObj [("Key", .str key), ("Note", .str value)]).toArray),
    ("Side", .arr (right.map fun (key, value) => Json.mkObj [("Key", .str key), ("Val", .str value)]).toArray)]

private def world : World := { now := { epochMillis := 0 } }

private def runOutcome (condition : String) (roots : List Json)
    (cache : Option MessageIndexCache := none) (rightError : Bool := false) :
    Option (Except String (List FlatRuleMessage)) := do
  let input ← (readDocument dm (.mkObj [("Et", .arr roots.toArray)])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let sourceRule := if rightError then
    { (rule condition) with group := ["Et", "Side"], errorEntityRelPath := "../Val" }
    else rule condition
  let plan ← (checkValidationRule dm .english sourceRule).toOption
  pure (runValidationRule world checked plan (messageCache := cache))

private def run (condition : String) (roots : List Json)
    (cache : Option MessageIndexCache := none) (rightError : Bool := false) :
    Option (List (String × String)) := do
  let outcome ← runOutcome condition roots cache rightError
  let messages ← outcome.toOption
  pure (messages.map fun message =>
    let observed := observe model message
    (observed.pointer, observed.messageType))

private def admitted (condition : String) : Bool :=
  (checkValidationRule dm .english (rule condition)).isOk

private def refusal (condition : String) : String :=
  match checkValidationRule dm .english (rule condition) with
  | .ok _ => "admitted"
  | .error reason => reason.detail

private def direct := "FieldFilled(/Et/Rows/Note) And FieldFilled(/Et/Side/Val)"
private def groups := "GroupFilled(/Et/Rows) And GroupFilled(/Et/Side)"
private def leftGroup := "GroupFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)"
private def rightGroup := "FieldFilled(/Et/Rows/Note) And GroupFilled(/Et/Side)"
private def rootDirect := "GroupFilled(/Et) And " ++ direct
private def leftOr := "GroupFilled(/Et/Rows) Or FieldFilled(/Et/Side/Val)"
private def profiles := [direct, groups, leftGroup, rightGroup, rootDirect, leftOr]
private def matched := root [("1", "left")] [("1", "right")]
private def crossParent := [root [("1", "left")] [("2", "right")],
  root [("2", "left")] [("1", "right")]]

example : model.validate.isOk = true := by native_decide

example : profiles.all (fun condition => admitted condition &&
    run condition [matched, matched] == some [
      ("Et/Rows/Note", "VALUE_ERROR"), ("Et[2]/Rows/Note", "VALUE_ERROR")]) = true := by native_decide

example : [groups, leftOr].all (fun condition =>
    run condition [root [("1", "")] [("1", "")], root [("1", "")] [("1", "")]] ==
      some [("Et/Rows/Note", "VALUE_ERROR"), ("Et[2]/Rows/Note", "VALUE_ERROR")]) = true ∧
    [direct, leftGroup, rightGroup, rootDirect].all (fun condition =>
      run condition [root [("1", "")] [("1", "")]] == some []) = true := by native_decide

example : [direct, groups, leftGroup, rightGroup, rootDirect].all
    (fun condition => run condition crossParent == some []) = true ∧
    run leftOr crossParent = some [
      ("Et/Rows/Note", "VALUE_ERROR"), ("/Et[1]/Rows[-5]/Note", "VALUE_ERROR"),
      ("/Et[2]/Rows[-5]/Note", "VALUE_ERROR"), ("Et[2]/Rows/Note", "VALUE_ERROR")] := by native_decide

example : run "GroupNotFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)"
    crossParent = some [
      ("/Et[1]/Rows[-5]/Note", "OMISSION_ERROR"), ("/Et[2]/Rows[-5]/Note", "OMISSION_ERROR")] ∧
    run "FieldFilled(/Et/Rows/Note) And GroupNotFilled(/Et/Side)"
      crossParent = some [
        ("Et/Rows/Note", "OMISSION_ERROR"), ("Et[2]/Rows/Note", "OMISSION_ERROR")] := by native_decide

example : run direct [] = some [] ∧ run groups [root [] []] = some [] ∧
    run groups [root [] [], matched] = some [("Et[2]/Rows/Note", "VALUE_ERROR")] ∧
    run groups [root [] [], root [] [], root [] [], root [] [], matched, matched] =
      some [("Et[5]/Rows/Note", "VALUE_ERROR")] := by native_decide

example : run "GroupNotFilled(/Et/Rows) And FieldFilled(/Et/Side/Val)"
    [root [("bad", "left")] [("1", "right")]] = some [] ∧
    run groups [root [("bad", "left")] [("1", "right")]] = some [] := by native_decide

example : [direct, groups, leftGroup, rightGroup, rootDirect].all (fun condition =>
    run condition [root [("bad", "left")] [("1", "right")],
      root [("1", "left")] [("bad", "right")]] == some []) = true ∧
    run leftOr [root [("bad", "left")] [("1", "right")],
      root [("1", "left")] [("bad", "right")]] = some [
        ("/Et[1]/Rows[-5]/Note", "VALUE_ERROR"), ("Et[2]/Rows/Note", "VALUE_ERROR")] ∧
    run "FieldFilled(/Et/Rows/Note) And GroupNotFilled(/Et/Side)"
      [root [("1", "left")] [("bad", "right")]] = some [] := by native_decide

example : ((checkParallelRule dm .english
    (rule "GroupFilled(RuleGroup) And FieldFilled(/Et/Side/Val)")).toOption.bind
      fun checked => match checked.condition with
        | .and (.leaf (.groupPresence _ reference)) _ => some reference
        | _ => none) =
      some { path := ["Et", "Rows"], origin := .ruleGroup, boundRepeatableScope := [9, 10] } ∧
    run "GroupFilled(RuleGroup) And FieldFilled(/Et/Side/Val)" [matched, matched] =
      run leftGroup [matched, matched] := by native_decide

example : ["GroupFilled(/Et) And FieldFilled(/Et/Side/Val)",
    "GroupFilled(/Et) Or FieldFilled(/Et/Side/Val)"].all
      (fun condition => refusal condition == "MVK_ERROR_FIELDGROUP_ITERATION5_INVALID") = true := by native_decide

example : !admitted "FieldFilled(/Et/Side/Val)" = true ∧
    !admitted "GroupNotFilled(/Et/Rows) And GroupNotFilled(/Et/Side)" = true ∧
    admitted "GroupFilled(/Et/Rows) And (GroupNotFilled(/Et/Rows) And GroupNotFilled(/Et/Side))" = true ∧
    !admitted "GroupFilled(/Et/Rows) Or (GroupNotFilled(/Et/Rows) And GroupNotFilled(/Et/Side))" = true ∧
    !admitted "GroupFilled(/Et) And FieldNotFilled(/Et/Rows/Note) And GroupNotFilled(/Et/Side)" = true ∧
    admitted "GroupFilled(/Et) And FieldFilled(/Et/Rows/Note) And GroupNotFilled(/Et/Side)" = true := by native_decide

private def runFailure (condition : String) (roots : List Json)
    (cache : Option MessageIndexCache := none) : Option String :=
  match runOutcome condition roots cache with
  | some (.error reason) => some reason
  | _ => none

/-- Without the actual cache association, -5 would falsely claim that no matching key exists (spec/08 §4.3). -/
example :
    let expected := some ((repr (ParallelPresenceRuleEvaluationError.join
      (.unresolvedDuplicatePointer 2 ["Et", "Rows"]))).pretty)
    runFailure leftOr [root [("1", "left"), ("1", "again")] [("1", "right")]] (some { insertions := [] }) = expected ∧
    runFailure leftOr [root [("0", "other"), ("2", "left"), ("2", "again")] [("2", "right")]] (some { insertions := [] }) = expected := by native_decide

private def duplicateRoot := root [("1", "left"), ("1", "again")] [("1", "right")]

example : run leftOr [duplicateRoot, root [] [], root [] [], root [] []] =
    some [("Et/Rows[2]/Note", "VALUE_ERROR")] ∧
    run leftOr [duplicateRoot, root [] [], root [] [], root [] [], root [] []] =
    some [("Et/Rows/Note", "VALUE_ERROR")] := by native_decide

private def hostCache (parent : Nat) (rows : List Nat) : MessageIndexCache := {
  insertions := rows.map fun row =>
    { group := 10, parentPath := [parent], key := .number 1, row } }

-- The cache-collision checkpoint in docs/sources/message-and-pointer-probes.md establishes that identical document inputs can yield both coordinates.
example : run leftOr [duplicateRoot] (some (hostCache 1 [1, 2])) =
    some [("Et/Rows[2]/Note", "VALUE_ERROR")] ∧
    run leftOr [duplicateRoot] (some (hostCache 1 [2, 1])) =
    some [("Et/Rows/Note", "VALUE_ERROR")] := by native_decide

example : run groups [duplicateRoot] (some (hostCache 1 [1, 2])) = some [] ∧
    run direct [duplicateRoot] (some (hostCache 1 [2, 1])) = some [] := by native_decide

example : run leftOr [duplicateRoot, duplicateRoot]
    (some { insertions := (hostCache 1 [1, 2]).insertions ++
      (hostCache 2 [2, 1]).insertions }) =
    some [("Et/Rows[2]/Note", "VALUE_ERROR"), ("Et[2]/Rows/Note", "VALUE_ERROR")] := by native_decide

example : run leftOr [matched] (some (hostCache 1 [2])) =
    run leftOr [matched] := by native_decide

example :
    let expected := some ((repr (ParallelPresenceRuleEvaluationError.join
      (.unresolvedDuplicatePointer 2 ["Et", "Rows"]))).pretty)
    runFailure leftOr [duplicateRoot] (some { insertions := [] }) = expected ∧
    runFailure leftOr [duplicateRoot] (some (hostCache 2 [2])) = expected ∧
    runFailure leftOr [duplicateRoot] (some { insertions := [
      { group := 20, parentPath := [1], key := .number 1, row := 2 },
      { group := 10, parentPath := [1], key := .text "1", row := 2 }] }) = expected := by native_decide

example :
    let rightCache : MessageIndexCache := { insertions := [
      { group := 20, parentPath := [1], key := .number 1, row := 1 },
      { group := 20, parentPath := [1], key := .number 1, row := 2 }] }
    let rightDuplicate := root [("1", "left")] [("1", "right"), ("1", "again")]
    run leftOr [rightDuplicate] (some rightCache) true =
      some [("Et/Side[2]/Val", "VALUE_ERROR")] ∧
    run leftOr [rightDuplicate] (some { insertions := rightCache.insertions.reverse }) true =
      some [("Et/Side/Val", "VALUE_ERROR")] := by native_decide

end A12Kernel.Dm.ParallelGroupRuleLocks
