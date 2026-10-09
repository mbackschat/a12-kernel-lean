import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.RepetitionNotUniqueLocks
open Lean A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [{
    id := 6, groupPath := ["Form", "Rows"], name := "Result"
    repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } }] }
private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }
private def data : DocumentData := {
  instantiatedRows := [1, 2, 3].map fun row => { group := 10, path := [row] }
  cells := [(1, "same", 2), (2, "other", 5), (3, "same", 7)].flatMap fun (row, tag, n) => [
    { address := { field := 3, path := [row] }, stored := tag, raw := .parsed (.str tag) },
    { address := { field := 4, path := [row] }, stored := toString n, raw := .parsed (.num n) }] }

private def repeated := "RepetitionNotUnique(/Form/Rows/Tag @From /Form/Rows)"
private def filtered := "Sum(/Form/Rows*/N Having [/Form/Rows/Tag] == [$/Form/Rows/Tag]) == 9"
private def fixedFilter := "Sum(/Form/Rows*/N Having [/Form/Rows/Tag] == \"same\") == 9"

private def ruleFor (condition : String) (rowHost : Bool := false) :=
  checkRule dm .english {
    group := if rowHost then ["Form", "Rows"] else ["Form"]
    name := "Duplicates", errorCode := "DUPLICATES", errorEntityRelPath := "/Form/Rows/Tag"
    condition := "FieldFilled(/Form/Rows/Tag) And (" ++ condition ++ ")", severity := "ERROR" }

private def run (condition : String) (rowHost : Bool := false) : Option (List Bool) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let rule ← (ruleFor condition rowHost).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun (_, outcome) => match outcome.verdict with | .fired _ => true | _ => false)

example : run filtered = some [true, false, true] ∧
    run filtered true = some [true, false, true] := by native_decide


example : [false, true].all (fun rowHost =>
    run repeated rowHost == some [true, false, true] &&
    run (repeated ++ " And " ++ filtered) rowHost == some [true, false, true] &&
    run (filtered ++ " And " ++ repeated) rowHost == some [true, false, true]) = true := by native_decide

private def lastRow := "Sum(/Form/Rows*/N Having [/Form/Rows/N] <= [$/Form/Rows/N]) == 14"
private def defaultScope := "RepetitionNotUnique(/Form/Rows/Tag)"
private def composite := "RepetitionNotUnique(/Form/Rows/Tag, /Form/Rows/N @From /Form/Rows)"

-- Spec/07 §6: a row excluded by the surrounding guard still makes its partner a duplicate.
example : run lastRow = some [false, false, true] ∧
    [false, true].all (fun rowHost =>
      run (lastRow ++ " And " ++ repeated) rowHost == some [false, false, true] &&
      run (repeated ++ " And " ++ lastRow) rowHost == some [false, false, true] &&
      run (lastRow ++ " Or " ++ repeated) rowHost == some [true, false, true] &&
      run (repeated ++ " Or " ++ lastRow) rowHost == some [true, false, true] &&
      run (composite ++ " And " ++ filtered) rowHost == some [false, false, false]) = true := by native_decide

example : run (defaultScope ++ " And " ++ filtered) = some [true, false, true] ∧
    run (filtered ++ " And " ++ defaultScope) = some [true, false, true] := by native_decide

private def originPreserved : Bool :=
  match ruleFor (defaultScope ++ " And " ++ filtered) with
  | .error _ => false
  | .ok rule =>
      rule.condition.rowGroup == ["Form", "Rows"] &&
      rule.condition.declaringGroup == ["Form"] &&
      rule.condition.core.wellFormedBool ["Form", "Rows"] ["Form"] &&
      !rule.condition.core.wellFormedBool ["Form", "Rows"] ["Form", "Rows"]

example : originPreserved = true := by native_decide

private def computationRefusal (guard : String) (rowTarget : Bool)
    (common : Bool := false) : Option String :=
  match lowerComputation model .english {
    group := ["Form"], name := "Total", targetRelPath := if rowTarget then "../Rows/Result" else "../Out"
    commonPrecondition := if common then some guard else none
    alternatives := [{ precondition := if common then none else some guard, operation := "1" }]
    errorCodesToSuppress := [] } with
  | .ok _ => none
  | .error error => some error.detail


example : [false, true].all (fun rowTarget =>
    computationRefusal repeated rowTarget == some "MVK_ERROR_INVALID_LANGUAGE_FEATURE") = true ∧
    [repeated ++ " And " ++ fixedFilter, fixedFilter ++ " And " ++ repeated].all (fun guard =>
      computationRefusal guard true == some "MVK_ERROR_INVALID_LANGUAGE_FEATURE" &&
      computationRefusal guard false == some "MVK_NO_WILDCARD") = true := by native_decide

example : [false, true].all (fun common =>
    computationRefusal fixedFilter true common == none &&
    [repeated, "CustomCondition Check"].all (fun forbidden =>
      [forbidden ++ " And " ++ fixedFilter, fixedFilter ++ " And " ++ forbidden].all fun guard =>
        computationRefusal guard true common == some "MVK_ERROR_INVALID_LANGUAGE_FEATURE")) = true := by native_decide

end A12Kernel.Dm.RepetitionNotUniqueLocks
