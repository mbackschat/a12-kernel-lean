import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.AncestorErrorScopeLocks
open Lean

private def model : FlatModel := {
  fields := [
    { id := 1, name := "RootFlag", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Marker", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 3, name := "Value", groupPath := ["Form", "Rows", "Sub"], repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Text", groupPath := ["Form", "Rows", "Sub"], repeatableScope := [10, 20], policy := { kind := .string } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
    { level := 20, path := ["Form", "Rows", "Sub"], repeatability := some 3 }] }

private def dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }

private def rule (condition : String) (error : String := "Text") : DmRule := {
  group := ["Form"], name := "Ancestor", errorCode := "ANCESTOR", severity := "ERROR"
  errorEntityRelPath := "../Rows/Sub/" ++ error, condition }

private def parent (marker : String) (children : List Json) : Json :=
  .mkObj [("Marker", .str marker), ("Sub", .arr children.toArray)]

private def document (rows : List Json) : Option (CheckedDocument model) := do
  let input ← (readDocument dm (.mkObj [("Form", .mkObj [
    ("RootFlag", .str "yes"), ("Rows", .arr rows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def run (condition : String) (rows : List Json) (error : String := "Text")
    (definition? : Option DmRule := none) : Option (List String) := do
  let checked ← (checkRule dm .english (definition?.getD (rule condition error))).toOption
  let document ← document rows
  pure ((← (runRule world document checked).toOption).map fun message => (observe model message).pointer)

private def observePartial (condition : String) (rows : List Json) (scope : ValidationRelevanceScope)
    (error : String := "Text") : Option (List String) := do
  let checked ← (checkRule dm .english (rule condition error)).toOption
  let document ← document rows
  let .evaluated outcomes ← (checked.evalOrdinaryRepeatablePartial document scope (some world)).toOption | none
  pure (outcomes.filterMap fun (_, outcome) => match outcome with
    | .skipped => none
    | .evaluated result => result.message?.map fun message => (observe model message).pointer)

example : model.validate.isOk = true := by native_decide

example : (checkRule dm .english { (rule "GroupFilled(Rows)") with
    errorEntityRelPath := "../Rows/Marker" }).isOk = true := by native_decide

example : run "GroupFilled(Rows)" [parent "present" [], parent "" [
    .mkObj [], .mkObj [], .mkObj [("Text", .str "third")]]] =
    some ["Form/Rows/Sub/Text", "Form/Rows[2]/Sub/Text"] := by native_decide

example : run "Sum(Rows/Sub*/Value) > 100" [
    parent "" [.mkObj [("Value", .str "200")]],
    parent "" [.mkObj [("Value", .str "50")]]] "Value" =
    some ["Form/Rows/Sub/Value"] := by native_decide

example : observePartial "GroupFilled(Rows)" [parent "present" [], parent "" [
    .mkObj [], .mkObj [], .mkObj [("Text", .str "third")]]] .full =
    some ["Form/Rows/Sub/Text", "Form/Rows[2]/Sub/Text"] := by native_decide

example : observePartial "GroupFilled(Rows)" [parent "present" [], parent "" [
    .mkObj [], .mkObj [], .mkObj [("Text", .str "third")]]]
    (.partialSet [{ path := ["Form", "Rows", "Sub", "Text"], indices := [.all, .concrete 2, .concrete 3, .all] }]) =
    some ["Form/Rows[2]/Sub/Text"] := by native_decide

private def populated := [parent "present" [], parent "" [
  .mkObj [], .mkObj [], .mkObj [("Text", .str "third")]]]

private def plan (definition : DmRule) :
    Option (Option (List RepeatableLevel) × List RepeatableLevel × OrdinaryRuleIterationPlan) :=
  (checkRule dm .english definition).toOption.map fun checked =>
    (checked.iterationScope, checked.errorDeclaration.repeatableScope, checked.ordinaryIterationPlan)

example : plan (rule "GroupFilled(Rows)") = some (some [10], [10, 20], .rows [10]) ∧
    plan { (rule "GroupFilled(Rows)") with errorEntityRelPath := "../Rows/Marker" } =
      some (some [10], [10], .rows [10]) ∧
    plan (rule "GroupFilled(/Form)") = some (none, [10, 20], .once [10, 20]) ∧
    plan (rule "Sum(Rows/Sub*/Value) > 100" "Value") =
      some (some [10], [10, 20], .rows [10]) := by native_decide

example : run "GroupFilled(Rows)" populated.reverse =
      some ["Form/Rows/Sub/Text", "Form/Rows[2]/Sub/Text"] ∧
    run "GroupFilled(Rows)" [parent "" [], populated[1]!] =
      some ["Form/Rows/Sub/Text", "Form/Rows[2]/Sub/Text"] ∧
    run "GroupFilled(Rows)" [populated[1]!, parent "" []] =
      some ["Form/Rows/Sub/Text", "Form/Rows[2]/Sub/Text"] ∧
    run "GroupFilled(Rows)" [parent "" [
      .mkObj [("Text", .str "first")], .mkObj [("Text", .str "second")], .mkObj [("Text", .str "third")]]]
      = some ["Form/Rows/Sub/Text"] := by native_decide

example : run "GroupFilled(Rows)" [parent "present" []] = some ["Form/Rows/Sub/Text"] := by native_decide

example : run "Sum(Rows/Sub*/Value) > 100" [
    parent "" [.mkObj [("Value", .str "200")]]] "Value" =
    some ["Form/Rows/Sub/Value"] := by native_decide

example : run "GroupFilled(Rows)" populated
      (definition? := some { (rule "GroupFilled(Rows)") with errorEntityRelPath := "../Rows/Marker" }) =
      some ["Form/Rows/Marker", "Form/Rows[2]/Marker"] ∧
    run "GroupFilled(/Form)" populated = some ["Form/Rows/Sub/Text"] ∧
    run "GroupFilled(/Form)" [] = some ["Form/Rows/Sub/Text"] := by native_decide

private def summed := [
  parent "present" [.mkObj [("Value", .str "80")], .mkObj [("Value", .str "80")]],
  parent "" [.mkObj [("Value", .str "200")]]]
private def sumCondition := "FieldFilled(Rows/Marker) And Sum(Rows/Sub*/Value) > 100"

example : run sumCondition summed "Value" = some ["Form/Rows/Sub/Value"] ∧
    run sumCondition summed.reverse "Value" = some ["Form/Rows[2]/Sub/Value"] ∧
    observePartial sumCondition summed .full "Value" = some ["Form/Rows/Sub/Value"] := by native_decide

private def childRelevant (parent child : Nat) : ValidationRelevanceScope :=
  .partialSet [{
    path := ["Form", "Rows", "Sub", "Text"]
    indices := [.all, .concrete parent, .concrete child, .all] }]

private def rowOutcome (environment : Env) (scope : ValidationRelevanceScope) :
    Option (Option (Verdict × Option String)) := do
  let checked ← (checkRule dm .english (rule "GroupFilled(Rows)")).toOption
  let document ← document populated
  let (_, outcome) ← (checked.evalOrdinaryRepeatablePartialAt document scope environment (some world)).toOption
  pure (match outcome with
    | .skipped => none
    | .evaluated result => some (result.verdict, result.message?.map fun message => (observe model message).pointer))

example : rowOutcome [(10, 2)] (childRelevant 2 3) =
      some (some (.fired .value, some "Form/Rows[2]/Sub/Text")) ∧
    rowOutcome [(10, 1)] (childRelevant 2 3) = some none ∧
    rowOutcome [(10, 2), (20, 3)] (childRelevant 2 3) =
      some (some (.fired .value, some "Form/Rows[2]/Sub/Text")) ∧
    observePartial "GroupFilled(Rows)" populated (childRelevant 1 3) =
      some ["Form/Rows/Sub/Text"] := by native_decide

private def errorPath (environment : Env) (definition : DmRule := rule "GroupFilled(Rows)") :
    Option (Except OrdinaryRepeatableRuleEvaluationError (List Nat)) :=
  (checkRule dm .english definition).toOption.map (·.errorPathAt environment)

private def pathMatches (actual : Option (Except OrdinaryRepeatableRuleEvaluationError (List Nat)))
    (expected : Except OrdinaryRepeatableRuleEvaluationError (List Nat)) : Bool :=
  match actual, expected with
  | some (.ok actual), .ok expected => actual == expected
  | some (.error actual), .error expected => decide (actual = expected)
  | _, _ => false

example : pathMatches (errorPath [(10, 2)]) (.ok [2, 1]) ∧
    pathMatches (errorPath [(20, 3), (10, 2)]) (.ok [2, 1]) ∧
    pathMatches (errorPath [(10, 2), (20, 0), (20, 3)]) (.ok [2, 1]) ∧
    pathMatches (errorPath []) (.error (.addressing (.environment (.missingBinding 10)))) ∧
    pathMatches (errorPath [(10, 0)]) (.error (.addressing (.environment (.zeroBinding 10)))) ∧
    pathMatches (errorPath [(10, 1), (10, 2)]) (.error (.addressing (.environment (.duplicateBinding 10)))) ∧
    pathMatches (errorPath [(10, 2), (20, 3)] (rule "GroupFilled(/Form)")) (.ok [1, 1]) := by native_decide

example : (document populated).map (fun document =>
    document.source.instantiatedRows.filter (·.group == 20) |>.map (·.path)) =
      some [[2, 1], [2, 2], [2, 3]] := by native_decide

private def childDeclaration : FlatFieldDecl := model.fields[3]'(by decide)
private def parentDeclaration : FlatFieldDecl := model.fields[1]'(by decide)
private def rootDeclaration : FlatFieldDecl := model.fields[0]'(by decide)

example :
    !(ruleErrorScopeCompatible true childDeclaration (some [10, 30])) ∧
    !(ruleErrorScopeCompatible true childDeclaration (some [20])) ∧
    !(ruleErrorScopeCompatible true parentDeclaration (some [10, 20])) ∧
    !(ruleErrorScopeCompatible true rootDeclaration (some [10])) ∧
    ruleErrorScopeCompatible true childDeclaration (some [10]) ∧
    ruleErrorScopeCompatible true childDeclaration (some [10, 20]) ∧
    ruleErrorScopeCompatible true childDeclaration none ∧
    !(ruleErrorScopeCompatible false childDeclaration none) := by native_decide

example :
    (checkRule dm .english (rule "FieldFilled(RootFlag) And FieldFilled(Rows/Sub/Text)")).isOk ∧
    !(checkRule dm .english { (rule "FieldFilled(RootFlag) And FieldFilled(Rows/Sub/Text)") with
      errorEntityRelPath := "../RootFlag" }).isOk ∧
    (checkRule dm .english (rule "FieldFilled(Rows/Marker) And FieldFilled(Rows/Sub/Text)")).isOk ∧
    !(checkRule dm .english { (rule "FieldFilled(Rows/Marker) And FieldFilled(Rows/Sub/Text)") with
      errorEntityRelPath := "../Rows/Marker" }).isOk := by native_decide

private def failureRows := [
  parent "" [.mkObj [("Text", .str "content")]],
  parent "present" [.mkObj [], .mkObj [], .mkObj [("Text", .str "third")]]]
private def failure := "GroupFilled(Rows) And Valid(Rows/Marker,\"Missing\")"

private def failureAt : Option (List (Env × Option String)) := do
  let checked ← (checkRule dm .english (rule failure)).toOption
  let document ← document failureRows
  pure ((← (checked.evalOrdinaryRepeatableFull document (some world)).toOption).map
    fun (environment, outcome) =>
      (environment, outcome.message?.map fun message => (observe model message).pointer))

example : failureAt = some [([(10, 1)], none),
    ([(10, 2)], some "Form/Rows/Sub/Text")] := by native_decide

example : run failure failureRows = some ["Form/Rows/Sub/Text"] ∧
    observePartial failure failureRows .full = some ["Form/Rows/Sub/Text"] ∧
    run ("FieldNotFilled(RootFlag) And (" ++ failure ++ ")") failureRows = some [] ∧
    observePartial ("FieldNotFilled(RootFlag) And (" ++ failure ++ ")") failureRows .full = some [] := by native_decide

end A12Kernel.Dm.AncestorErrorScopeLocks
