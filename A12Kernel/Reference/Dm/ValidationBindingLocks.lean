import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # Declaring paths and error-field iteration binding

The peer cart rule calibrates a root-declared coordinate read at a row error field. Distinct
same-named fields make replacing lexical scope with the target group observably wrong.
-/
namespace A12Kernel.Dm.ValidationBindingLocks
open A12Kernel A12Kernel.Dm Lean

private def number (id : FieldId) (group : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, name, groupPath := group, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } } }
private def model : FlatModel := {
  fields := [number 1 ["Form"] "Qty", number 2 ["Form", "Rows"] "Qty" [10],
    number 4 ["Form", "Side"] "SideQty",
    { id := 3, name := "Key", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def rule (text : String) : DmRule := {
  group := ["Form"], name := "Rule", errorCode := "R", errorEntityRelPath := "../Rows/Qty"
  condition := text, severity := "ERROR" }
private def row (qty key : String) : Json := Json.mkObj [("Qty", Json.str qty), ("Key", Json.str key)]

private def capturedRepetitionFilter :=
  "Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows)"

example : ["AtLeastOneFieldFilled", "MoreThanOneFieldFilled"].all (fun operator =>
    match checkRule dm .english (rule (operator ++ "(" ++ capturedRepetitionFilter ++ ")")) with
    | .error refusal => refusal.construct == "RuleAssembly" &&
        refusal.detail == (FlatRuleAssemblyError.negativeConditionInIteration 10).refusalDetail
    | .ok _ => false) := by native_decide

example : (checkRule dm .english
    (rule ("AllFieldsFilled(" ++ capturedRepetitionFilter ++ ")"))).isOk = true := by native_decide

example : (checkRule dm .english {
      (rule ("AllFieldsFilled(" ++ capturedRepetitionFilter ++ ")")) with
      errorEntityRelPath := "../Rows/Key" }).isOk = true := by native_decide

example : (match checkRule dm .english {
      (rule ("AtLeastOneFieldFilled(" ++ capturedRepetitionFilter ++ ")")) with
      errorEntityRelPath := "../Rows/Key" } with
    | .error refusal => refusal.construct == "RuleAssembly" &&
        refusal.detail == (FlatRuleAssemblyError.negativeConditionInIteration 10).refusalDetail
    | .ok _ => false) = true := by native_decide

private def nestedRepetitionCases : List String := [
  "AllFieldsFilled(Rows*/Qty Having CurrentRepetition(Rows) + 1 != CurrentRepetition($Rows) + 1)",
  "MaxValue(" ++ capturedRepetitionFilter ++ ") > 0",
  "AllFieldsFilled(Rows*/Qty Having CurrentRepetition(Rows) > 0 And DayFromDate(AddDays(Date(\"01\",\"01\",\"2024\"),CurrentRepetition($Rows))) > 0)",
  "AllFieldsFilled(Rows*/Qty Having CurrentRepetition(Rows) > 0 And DifferenceInDays(AddDays(Date(\"01\",\"01\",\"2024\"),CurrentRepetition($Rows)),Date(\"01\",\"01\",\"2024\")) > 0)",
  "AllFieldsFilled(Rows*/Qty Having CurrentRepetition(Rows) > 0 And AddDays(Date(\"01\",\"01\",\"2024\"),CurrentRepetition($Rows)) > Date(\"01\",\"01\",\"2024\"))"]

private def repetitionReferenceSummary (text : String) :
    Option (Bool × Bool × Option Bool × Option Bool) := do
  let checked ← (checkRule dm .english {
    (rule text) with errorEntityRelPath := "../Rows/Key" }).toOption
  pure (checked.condition.core.referencesField 3, checked.condition.core.referencesErrorField 3,
    checked.condition.core.authoredErrorReference? 3, checked.condition.core.errorReferenceAt? 3 10)

example : nestedRepetitionCases.all (fun text =>
    repetitionReferenceSummary text == some (false, true, some true, some true)) = true := by native_decide

example : (match checkRule dm .english {
    (rule "AllFieldsFilled(Rows*/Qty Having CurrentRepetition(Rows) > 0)") with
    errorEntityRelPath := "../Rows/Key" } with
  | .error refusal => refusal.construct == "RuleAssembly" &&
      refusal.detail == (FlatRuleAssemblyError.errorFieldNotReferenced 3).refusalDetail
  | .ok _ => false) = true := by native_decide

private def fixedModel : FlatModel := { model with
  fields := model.fields ++ [number 5 ["Form", "Rows", "Box"] "NestedQty" [10],
    number 6 ["Form", "Rows", "Sibling"] "NestedQty" [10]] }
private def fixedDm : DmModel := { dm with flat := fixedModel }
private def fixedRepetitionFilter :=
  "Rows*/Qty Having CurrentRepetition(Rows/Box) == CurrentRepetition($Rows/Box)"

private def fixedReferenceSummary :
    Option (Bool × Bool × Bool × Option Bool × Option Bool × Option Bool) := do
    let checked ← (checkRule fixedDm .english {
      (rule ("AllFieldsFilled(" ++ fixedRepetitionFilter ++ ")")) with
      errorEntityRelPath := "../Rows/Box/NestedQty" }).toOption
    pure (checked.condition.core.referencesField 5,
      checked.condition.core.referencesErrorField 5, checked.condition.core.referencesErrorField 6,
      checked.condition.core.errorReferenceAt? 5 10,
      checked.condition.core.messageGroupReference? 5 ["Form", "Rows", "Box"],
      checked.condition.core.messageGroupReference? 5 ["Form", "Rows", "Sibling"])

example : (fixedReferenceSummary ==
    some (false, true, false, some true, some true, some false)) = true := by native_decide

example : (match checkRule fixedDm .english {
    (rule ("AtLeastOneFieldFilled(" ++ fixedRepetitionFilter ++ ")")) with
    errorEntityRelPath := "../Rows/Box/NestedQty" } with
  | .error refusal => refusal.construct == "RuleAssembly" &&
      refusal.detail == (FlatRuleAssemblyError.negativeConditionInIteration 10).refusalDetail
  | .ok _ => false) = true := by native_decide

private def run (text : String) (rows : List Json) (errorField : String := "../Rows/Qty") : Option (List String) := do
  let checkedRule ← (checkRule dm .english { (rule text) with errorEntityRelPath := errorField }).toOption
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Qty", "9"), ("Rows", Json.arr rows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world document checkedRule).toOption).map fun message => (observe model message).pointer)

example : run "FieldFilled(Rows/Key) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows))"
    [row "5" "A", row "7" "B"] "../Rows/Key" =
    some ["Form/Rows/Key", "Form/Rows[2]/Key"] := by native_decide

example : run "[Rows/Key] PatternMatched \"[0-9]+\""
    [row "5" "123", row "5" "x123"] "../Rows/Key" = some ["Form/Rows/Key"] ∧
    run "[Rows/Key] PatternViolated {{\"[0-9]+\"}}"
    [row "5" "123", row "5" "x123"] "../Rows/Key" = some ["Form/Rows[2]/Key"] ∧
    run "[Rows/Key] PatternViolated \"[0-9]+\""
    [row "5" "", row "5" ""] "../Rows/Key" = some [] := by native_decide

example : run "FieldFilled(Qty) And [Rows/Key] PatternMatched \"[0-9]+\""
    [row "5" "123", row "5" "x123"] "../Rows/Key" = some ["Form/Rows/Key"] := by native_decide

example : run "(FieldNotFilled(Qty) And FieldFilled(Rows/Key)) Or [Rows/Key] PatternViolated \"[0-9]+\""
    [row "5" "123", row "5" "x123"] "../Rows/Key" = some ["Form/Rows[2]/Key"] := by native_decide

example : (do
    let checked ← (checkRule dm .english {
      (rule "[Rows/Key] PatternMatched \"[0-9]+\"") with errorEntityRelPath := "../Rows/Key" }).toOption
    pure (checked.condition.declaringGroup, checked.condition.rowGroup)) =
      some (["Form"], ["Form", "Rows"]) := by native_decide

example :
    let field : SurfaceFieldPath := { base := .absolute, groups := ["Form", "Rows"], field := "Key" }
    (model.resolveFieldDeclarationUnchecked ["Form", "Side"] field).isOk = true ∧
    (elaborateStringPatternCondition builtinStringPatternCompiler model ["Form", "Side"]
      { op := .matched, field, source := "[0-9]+" } ["Form", "Rows"]).isOk = false := by native_decide

private def partialPatternRows : Option (List (Env × Verdict)) := do
  let checked ← (checkRule dm .english {
    (rule "[Rows/Key] PatternMatched \"[0-9]+\"") with errorEntityRelPath := "../Rows/Key" }).toOption
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", Json.arr [row "5" "123", row "5" "x"].toArray)])])).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  match ← (checked.evalOrdinaryRepeatablePartial document .full).toOption with
  | .skipped => none
  | .evaluated rows => rows.mapM fun (environment, outcome) => match outcome with
      | .skipped => none
      | .evaluated result => some (environment, result.verdict)

example : partialPatternRows = some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] := by native_decide

example : (checkRule dm .english {
    (rule "[/Form/Rows/Key] PatternMatched \"[0-9]+\"") with
    group := ["Form", "Side"], errorEntityRelPath := "../../Rows/Key" }).isOk = false ∧
    (checkRule dm .english {
      (rule "[Rows/Key] PatternMatched \"[0-9]+\"") with errorEntityRelPath := "../Qty" }).isOk = false := by native_decide

example : run "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1"
    [row "5" "A", row "5" "B"] = some ["Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1" [row "5" "A"] = some [] := by native_decide

example : run "FieldFilled(Rows/Qty) And [Qty] + [Rows/Qty] > 10"
    [row "2" "A", row "1" "B"] = some ["Form/Rows/Qty"] := by native_decide

example : run "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1 And [Qty] + 1 > 0"
    [row "5" "A", row "5" "B"] = some ["Form/Rows[2]/Qty"] := by native_decide

example : run "AllFieldsFilled(Rows/Qty, Rows/Key)"
    [row "2" "A", row "1" ""] = some ["Form/Rows/Qty"] ∧
    run "AllFieldsFilled(Rows/Qty, Rows/Key)" [row "2" "", row "1" "B"] =
      some ["Form/Rows[2]/Qty"] ∧
    run "AllFieldsFilled(Rows/Qty, Rows/Key)" [] = some [] := by native_decide

example : run "FieldFilled(Rows/Qty) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows))"
    [row "5" "A", row "7" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows))"
    [row "5" "A"] = some [] := by native_decide

example : (do
    let checked ← (checkRule dm .english
      (rule "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1")).toOption
    pure (checked.condition.declaringGroup, checked.condition.rowGroup, checked.iterationScope)) =
    some (["Form"], ["Form", "Rows"], some [10]) := by native_decide

example : (do
    let root ← (checkRule dm .english (rule "AllFieldsFilled(Rows/Qty, Rows/Key)")).toOption
    let localRule ← (checkRule dm .english { (rule "AllFieldsFilled(Qty, Key)") with
      group := ["Form", "Rows"]
      errorEntityRelPath := "../Qty" }).toOption
    match root.condition.and localRule.condition with
    | .error (.declaringGroupMismatch left right) => some (left, right)
    | _ => none) = some (["Form"], ["Form", "Rows"]) := by native_decide

example :
    (checkRule dm .english
      (rule "FieldFilled(/Form/Rows/Qty) And CurrentRepetition(/Form/Rows) > 1")).isOk = true ∧
    (checkRule dm .english {
      (rule "FieldFilled(/Form/Rows/Qty) And CurrentRepetition(/Form/Rows) > 1") with
      group := ["Form", "Side"]
      errorEntityRelPath := "../../Rows/Qty" }).isOk = false := by native_decide

example : run "FieldFilled(Rows/Qty) And [Rows/Qty] < MaxValue(Rows*/Qty Having CurrentRepetition(Rows) < CurrentRepetition($Rows))"
    [row "3" "A", row "1" "B"] = some ["Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And [Rows/Qty] < MaxValue(Rows*/Qty Having CurrentRepetition(Rows) < CurrentRepetition($Rows))"
    [row "3" "A", row "4" "B"] = some [] := by native_decide

example : run "FieldFilled(Rows/Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] == [$Rows/Qty] And CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 0"
    [row "5" "A", row "5" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] == [$Rows/Qty] And CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 0"
    [row "5" "A"] = some [] := by native_decide

example : run "FieldFilled(Rows/Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] > [Qty] And CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 10"
    [row "12" "A", row "5" "B"] = some ["Form/Rows[2]/Qty"] := by native_decide

example : run "FieldFilled(Rows/Qty) And NumberOfDifferentValues(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows)) == 1"
    [row "5" "A", row "5" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And NumberOfDifferentValues(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows)) == 1"
    [row "5" "A"] = some [] := by native_decide

example : (checkRule dm .english {
      (rule "FieldFilled(Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] > 0) > 0") with
      errorEntityRelPath := "../Qty" }).isOk = true ∧
    (checkRule dm .english {
      (rule "FieldFilled(Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] == [$Rows/Qty]) > 0") with
      errorEntityRelPath := "../Qty" }).isOk = false := by native_decide

example : (do
    let checked ← (checkRule dm .english (rule
      "FieldFilled(Rows/Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] > [Qty] And CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 10")).toOption
    pure (checked.condition.core.anyLeaf fun
      | .orderedNumeric _ comparison => comparison.left.anyAtom fun
          | .aggregate _ source => source.operands.any fun
              | .starHaving filtered => filtered.declaringGroup == ["Form"] &&
                  filtered.bindingGroup == ["Form", "Rows"] && filtered.having.fieldIds == [2, 1]
              | _ => false
          | _ => false
      | _ => false)) = some true := by native_decide

example : run "FieldFilled(Rows/Qty) And MaxValue(Rows/Qty, Rows*/Qty Having CurrentRepetition(Rows) == 1) > 5"
    [row "1" "A", row "7" "B"] = some ["Form/Rows[2]/Qty"] := by native_decide

example : run "FieldFilled(Rows/Qty) And Sum(Rows/Qty, Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 0"
    [row "3" "A", row "1" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And FirstFilledValue(Rows/Qty, Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 0"
    [row "3" "A", row "1" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] := by native_decide

example : run "FieldFilled(Rows/Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] == [$Rows/Qty] And CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 0"
    [row "5" "A", row "7" "B"] = some [] ∧
    run "FieldFilled(Rows/Qty) And MaxValue(Rows*/Qty Having [Rows/Qty] == [Rows/Qty] And CurrentRepetition(Rows) != CurrentRepetition($Rows)) > 0"
    [row "5" "A", row "7" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] := by native_decide

example : run "FieldFilled(Rows/Qty) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows) And [Rows/Qty] == [$Rows/Qty])"
    [row "5" "A", row "5" "B"] = some ["Form/Rows/Qty", "Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows) And [Rows/Qty] == [$Rows/Qty])"
    [row "5" "A", row "7" "B"] = some [] ∧
    run "FieldFilled(Rows/Qty) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows) And [Rows/Qty] == [$Rows/Qty])"
    [row "5" "A"] = some [] := by native_decide

example : (do
    let checked ← (checkRule dm .english
      (rule "FieldFilled(Rows/Qty) And AtLeastOneFieldFilled(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows))")).toOption
    let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
      ("Rows", Json.arr [row "5" "A", row "5" "B"].toArray)])])).toOption
    let world : World := { now := { epochMillis := 0 } }
    let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
    let document ← (checkDocument prepared "en_US" input.data).toOption
    let partialResult ← (checked.evalOrdinaryRepeatablePartial document .full).toOption
    pure (checked.hasHaving, partialResult)) = some (true, .skipped) := by native_decide

example : (do
    let checked ← (checkRule dm .english {
      (rule "FieldFilled(Qty) And AtLeastOneFieldFilled(Rows*/Qty Having [Rows/Qty] > [Side/SideQty])") with
      errorEntityRelPath := "../Qty" }).toOption
    pure (checked.condition.core.referencesField 4, checked.condition.core.referencesErrorField 4,
      checked.condition.core.referencesField 2)) = some (true, false, true) := by native_decide

-- The shared full-validation domain may bind an absent row. Both operand orders
-- must read its direct Number cell as empty while the star retains physical topology.
example : run "FirstFilledValue(Rows/Qty, Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows)) + 0 > 1"
    [] = some [] ∧
    run "FirstFilledValue(Rows*/Qty Having CurrentRepetition(Rows) != CurrentRepetition($Rows), Rows/Qty) + 0 > 1"
    [] = some [] := by native_decide

end A12Kernel.Dm.ValidationBindingLocks
