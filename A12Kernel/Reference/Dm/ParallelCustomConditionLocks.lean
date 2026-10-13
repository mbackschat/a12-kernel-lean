import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document

/-! Reader-to-evaluator controls for a custom-condition leaf in a parallel rule. The staffing model
mirrors the retained `staffing-coverage-pair` shape: two keyed repeatable groups under one
non-repeatable root, with the error field on the Demand side. The nested model adds an outer
repeatable level to pin the pointer's outer coordinate. Kernel runtime calibration of the callback
payload is not retained; these locks are internal. -/
namespace A12Kernel.Dm.ParallelCustomConditionLocks
open Lean

private def field (id : FieldId) (group name : String) (kind : FieldKind) : FlatFieldDecl := {
  id, name, groupPath := ["Staffing", group], repeatableScope := [if group == "Demand" then 10 else 20]
  policy := { kind } }
private def number (id : FieldId) (group : String) : FlatFieldDecl :=
  field id group "Headcount" (.number { scale := 0, signed := false })
private def model : FlatModel := {
  fields := [field 1 "Demand" "Department" .string, number 2 "Demand",
    field 3 "Supply" "Department" .string, number 4 "Supply"]
  repeatableGroups := [
    { level := 10, path := ["Staffing", "Demand"], repeatability := some 20, indexField := some 1 },
    { level := 20, path := ["Staffing", "Supply"], repeatability := some 20, indexField := some 3 }] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (condition : String) : DmRule := {
  group := ["Staffing"], name := "Cover", errorCode := "COVER", severity := "ERROR",
  errorEntityRelPath := "../Demand/Headcount", condition }

private def world : World := { now := { epochMillis := 0 } }

private def rows (entries : List (String × String)) : Json :=
  .arr (entries.map fun (key, count) =>
    Json.mkObj [("Department", .str key), ("Headcount", .str count)]).toArray

private def checkedOf (dm : DmModel) (data : Json) : Option (CheckedDocument dm.flat) := do
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def document (demand supply : List (String × String)) : Option (CheckedDocument dm.flat) :=
  checkedOf dm (.mkObj [("Staffing", .mkObj [("Demand", rows demand), ("Supply", rows supply)])])

private abbrev Outcome := Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome)

private def fullRun (source : DmRule) (dm : DmModel) (checked : CheckedDocument dm.flat)
    (registry : CustomValidationRegistry dm.flat) : Option Outcome := do
  let plan ← (checkParallelRule dm .english source).toOption
  let preliminary ← checked.applyFullIndexPreliminary.toOption
  pure (plan.evalDocument preliminary none registry)

private def partialRun (source : DmRule) (dm : DmModel) (checked : CheckedDocument dm.flat)
    (registry : CustomValidationRegistry dm.flat) : Option Outcome := do
  let plan ← (checkParallelRule dm .english source).toOption
  let view ← (checked.applyPartialGeneratedPreliminary
    [RelevantEntityPattern.allInstances (source.group.take 1)]).toOption
  pure (plan.evalPartialDocument view none registry)

private abbrev Route := DmRule → (dm : DmModel) → CheckedDocument dm.flat →
  CustomValidationRegistry dm.flat → Option Outcome

private abbrev Coordinates := List (List MessageRepetitionCoordinate)

private def errorCoordinates (outcome : Outcome) : Option Coordinates :=
  outcome.toOption.map (·.filterMap fun row => row.outcome.message?.map (·.errorAddress.coordinates))

private def failure (outcome : Outcome) : Option ParallelPresenceRuleEvaluationError :=
  match outcome with | .error error => some error | .ok _ => none

private def registered (callback : CustomValidationInvocation flat → Bool) : CustomValidationRegistry flat :=
  { configured := some fun name => if name == "Check" then some callback else none }

private def row (index : Nat) : List MessageRepetitionCoordinate := [.concrete index]
private def unmatched : List MessageRepetitionCoordinate := [.unknown]
private def nestedRow (outer index : Nat) : List MessageRepetitionCoordinate := [.concrete outer, .concrete index]
private def nestedUnmatched (outer : Nat) : List MessageRepetitionCoordinate := [.concrete outer, .unknown]

private def control := "FieldsNotCollectivelyFilled(Demand/Headcount, Supply/Headcount)"
private def custom := "CustomCondition Check"
private def bothFilled := "FieldFilled(Demand/Headcount) And FieldFilled(Supply/Headcount)"

private def admitted (condition : String) : Bool :=
  (checkParallelRule dm .english (rule condition)).isOk

-- The `Or` form's unguarded custom branch fails the parallel guard that its two `And` twins pass.
example : admitted control = true ∧ admitted (control ++ " And " ++ custom) = true ∧
    admitted (custom ++ " And " ++ control) = true ∧ admitted (control ++ " Or " ++ custom) = false ∧
    admitted (control ++ " Or " ++ control) = true := by native_decide

/-- The class the whole-rule check reports for a refused condition, `none` when it admits it. -/
private def refusalClass (condition : String) : Option String :=
  match checkValidationRule dm .english (rule condition) with
  | .error refusal => some refusal.detail
  | .ok _ => none

/- An unguarded parallel tree draws the parallel-iteration class through the whole-rule check, measured
on the `Or` row of this model and on two negative presence leaves in the diagnostic sweep; the guarded
`And` twin is admitted. -/
example :
    refusalClass (control ++ " Or " ++ custom) = some "MVK_PARALLEL_ITERATION_INVALID" ∧
    refusalClass "FieldNotFilled(Demand/Headcount) And FieldNotFilled(Supply/Headcount)" =
      some "MVK_PARALLEL_ITERATION_INVALID" ∧
    refusalClass (control ++ " And " ++ custom) = none := by native_decide

example : [control ++ " And " ++ custom, custom ++ " And " ++ control].all (fun condition =>
    match checkValidationRule dm .english (rule condition) with
    | .ok (.parallel _) => true
    | _ => false) = true := by native_decide

-- Keys A and C are Supply-empty or unmatched; B is filled on both sides; D exists on Supply only.
private def mixed := document [("A", "5"), ("B", "5"), ("C", "5")] [("A", ""), ("B", "7"), ("D", "7")]
private def fired (route : Route) (condition : String)
    (registry : CustomValidationRegistry dm.flat := {}) : Option Coordinates :=
  mixed.bind (fun checked => route (rule condition) dm checked registry) |>.bind errorCoordinates

private def routes : List Route := [fullRun, partialRun]

-- A custom leaf that holds leaves the pair's own firing rows untouched; one that fails silences them.
example : routes.all (fun route =>
    fired route control == some [row 1, row 3, unmatched] &&
    fired route (control ++ " And " ++ custom) (registered fun _ => true) == some [row 1, row 3, unmatched] &&
    fired route (control ++ " And " ++ custom) (registered fun _ => false) == some [] &&
    fired route (custom ++ " And " ++ control) (registered fun _ => true) == some [row 1, row 3, unmatched]) = true := by
  native_decide

-- Lookup happens when the fold reaches the leaf. A clean-false presence leaf ends the `And` before
-- it; `Check` stays unregistered, so only a reached row reports the missing registration.
private def reachless := document [("A", "5"), ("C", "5")] [("A", "")]
private def reaching := document [("B", "5")] [("B", "7")]
private def missing : ParallelPresenceRuleEvaluationError := .customCondition (.missingRegistration "Check")

example : routes.all (fun route =>
    (reachless.bind fun checked => (route (rule (bothFilled ++ " And " ++ custom)) dm checked {})
      |>.bind errorCoordinates) == some [] &&
    (reaching.bind fun checked => (route (rule (bothFilled ++ " And " ++ custom)) dm checked {})
      |>.bind failure) == some missing &&
    (reachless.bind fun checked => (route (rule (custom ++ " And " ++ bothFilled)) dm checked {})
      |>.bind failure) == some missing) = true := by native_decide

-- A fill quantifier's non-firing result is UNKNOWN, not a decided false, so it does not end an `And`.
example : routes.all (fun route =>
    (reaching.bind fun checked => (route (rule (control ++ " And " ++ custom)) dm checked {})
      |>.bind failure) == some missing) = true := by native_decide

-- Unmatched Demand key D has no Demand row: its error pointer carries the unknown coordinate.
private def pointerIs (coordinates : List MessageRepetitionCoordinate) :
    CustomValidationRegistry dm.flat :=
  registered fun input => input.errorPointer == { field := 2, coordinates }

example : routes.all (fun route =>
    fired route (control ++ " And " ++ custom) (pointerIs (row 1)) == some [row 1] &&
    fired route (control ++ " And " ++ custom) (pointerIs (row 3)) == some [row 3] &&
    fired route (control ++ " And " ++ custom) (pointerIs unmatched) == some [unmatched]) = true := by
  native_decide

-- Full validation passes the all-relevant marker; partial validation passes its normalized set.
private def relevanceIs (full : Bool) (scope : ValidationRelevanceScope) : CustomValidationRegistry dm.flat :=
  registered fun input => match input.relevance with
    | .all => full
    | .partialEntities actual => !full && actual == scope

example : (do
    let checked ← mixed
    let scope := (← (checked.applyPartialGeneratedPreliminary
      [RelevantEntityPattern.allInstances ["Staffing"]]).toOption).relevance
    let condition := control ++ " And " ++ custom
    pure ([
      fullRun (rule condition) dm checked (relevanceIs true scope),
      fullRun (rule condition) dm checked (relevanceIs false scope),
      partialRun (rule condition) dm checked (relevanceIs false scope),
      partialRun (rule condition) dm checked (relevanceIs true scope)].map (·.bind errorCoordinates))) =
    some [some [row 1, row 3, unmatched], some [], some [row 1, row 3, unmatched], some []] := by
  native_decide

-- The base document's findings reach the callback; row A still fires, and B is UNKNOWN on both sides.
example : (do
    let checked ← document [("A", "5"), ("B", "bad")] [("A", ""), ("B", "bad")]
    let findings : List CellAddr := [{ field := 2, path := [2] }, { field := 4, path := [2] }]
    let registry := registered fun input => input.formallyIncorrect.length == 2 &&
      findings.all input.formallyIncorrect.contains
    pure (routes.map fun route =>
      (route (rule (control ++ " And " ++ custom)) dm checked registry).bind errorCoordinates)) =
    some [some [row 1], some [row 1]] := by native_decide

-- An outer repeatable level contributes its concrete row to the pointer, for matched and unmatched keys.
private def nested : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Et", "Rows"], repeatableScope := [9, 10], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 2, name := "Note", groupPath := ["Et", "Rows"], repeatableScope := [9, 10], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 3, name := "Key", groupPath := ["Et", "Side"], repeatableScope := [9, 20], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 4, name := "Val", groupPath := ["Et", "Side"], repeatableScope := [9, 20], policy := { kind := .number { scale := 0, signed := false } } } ]
  repeatableGroups := [
    { level := 9, path := ["Et"], repeatability := some 5 },
    { level := 10, path := ["Et", "Rows"], repeatability := some 5, indexField := some 1 },
    { level := 20, path := ["Et", "Side"], repeatability := some 5, indexField := some 3 } ] }

private def nestedDm : DmModel := {
  flat := nested, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def nestedRule : DmRule := {
  group := ["Et", "Rows"], name := "Cover", errorCode := "COVER", severity := "ERROR",
  errorEntityRelPath := "../Note",
  condition := "FieldsNotCollectivelyFilled(/Et/Rows/Note, /Et/Side/Val) And CustomCondition Check" }

private def nestedRoot (left right : List (String × String)) : Json :=
  .mkObj [
    ("Rows", .arr (left.map fun (key, value) => Json.mkObj [("Key", .str key), ("Note", .str value)]).toArray),
    ("Side", .arr (right.map fun (key, value) => Json.mkObj [("Key", .str key), ("Val", .str value)]).toArray)]

private def nestedPointerIs (coordinates : List MessageRepetitionCoordinate) : CustomValidationRegistry nestedDm.flat :=
  registered fun input => input.errorPointer == { field := 2, coordinates }

example : (do
    let checked ← checkedOf nestedDm (.mkObj [("Et", .arr #[
      nestedRoot [("1", "10")] [("1", "30")],
      nestedRoot [("1", "20")] [("1", ""), ("3", "40")]])])
    pure ([fullRun, partialRun].map fun route =>
      [nestedRow 2 1, nestedUnmatched 2, nestedRow 1 1].map fun coordinates =>
        (route nestedRule nestedDm checked (nestedPointerIs coordinates)).bind errorCoordinates)) =
    some (List.replicate 2 [some [nestedRow 2 1], some [nestedUnmatched 2], some []]) := by
  native_decide

end A12Kernel.Dm.ParallelCustomConditionLocks
