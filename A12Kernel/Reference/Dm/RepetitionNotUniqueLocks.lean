import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.ValidationCondition.Omission

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
    computationRefusal repeated rowTarget ==
      some (if rowTarget then "MVK_ERROR_INVALID_LANGUAGE_FEATURE" else "MVK_NO_WILDCARD")) = true ∧
    [repeated ++ " And " ++ fixedFilter, fixedFilter ++ " And " ++ repeated].all (fun guard =>
      computationRefusal guard true == some "MVK_ERROR_INVALID_LANGUAGE_FEATURE" &&
      computationRefusal guard false == some "MVK_NO_WILDCARD") = true := by native_decide

example : [false, true].all (fun common =>
    computationRefusal fixedFilter true common == none &&
    [repeated, "CustomCondition Check"].all (fun forbidden =>
      [forbidden ++ " And " ++ fixedFilter, fixedFilter ++ " And " ++ forbidden].all fun guard =>
        computationRefusal guard true common == some "MVK_ERROR_INVALID_LANGUAGE_FEATURE")) = true := by native_decide

private def siblingModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with groupPath := ["Form", "Rows", "Left"] }
  else if field.id == 4 then { field with groupPath := ["Form", "Rows", "Right"] }
  else field }

private def siblingRun (explicitScope duplicate : Bool)
    (reverse unequalFirst : Bool := false) : Option (List Bool) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler siblingModel).toOption
  let input := { data with cells := data.cells.map fun cell =>
    if duplicate && cell.address == { field := 4, path := [3] } then
      { cell with stored := "2", raw := .parsed (.num 2) }
    else if unequalFirst && cell.address == { field := 3, path := [3] } then
      { cell with stored := "different", raw := .parsed (.str "different") }
    else cell }
  let document ← (checkDocument prepared "en_US" input).toOption
  let keys := if reverse then "Rows/Right/N, Rows/Left/Tag" else "Rows/Left/Tag, Rows/Right/N"
  let rule ← (checkRule { dm with flat := siblingModel } .english {
    group := ["Form"], name := "Siblings", errorCode := "DUPLICATES",
    errorEntityRelPath := "/Form/Rows/Left/Tag", severity := "ERROR",
    condition := "RepetitionNotUnique(" ++ keys ++
      (if explicitScope then " @From Rows)" else ")") }).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun (_, outcome) => match outcome.verdict with | .fired _ => true | _ => false)

-- The paired-gate oracle admits sibling fixed keys (inbound-2026-09-26k); spec/07 §6 compares
-- the complete composite key, so equality of just the first component must not fire.
example : [false, true].all (fun explicitScope =>
    [false, true].all (fun reverse =>
      siblingRun explicitScope true reverse == some [true, false, true] &&
      siblingRun explicitScope false reverse == some [false, false, false] &&
      siblingRun explicitScope true reverse true == some [false, false, false])) = true := by native_decide

private def siblingAdmission (condition : String) : Option String :=
  match checkRule { dm with flat := siblingModel } .english {
    group := ["Form"], name := "Siblings", errorCode := "DUPLICATES",
    errorEntityRelPath := "/Form/Rows/Left/Tag", severity := "ERROR",
    condition := "FieldFilled(Rows/Left/Tag) And " ++ condition } with
  | .ok _ => none
  | .error refusal => some refusal.detail

private def siblingRefusals : List (String × KernelStaticDiagnostic) := [
  ("RepetitionNotUnique(Rows/Left/Tag, Rows/Left/Tag)", .duplicateParam1),
  ("RepetitionNotUnique(Rows/Left, Rows/Left/Tag)", .duplicateParam2),
  ("RepetitionNotUnique(Rows/Left/Tag, Rows/Left)", .duplicateParam2),
  ("RepetitionNotUnique(Rows/Left)", .noGroupsAllowed),
  ("RepetitionNotUnique(/Form, Rows/Left/Tag)", .duplicateParam2),
  ("RepetitionNotUnique(Rows/Left/Tag, /Form)", .duplicateParam2),
  ("RepetitionNotUnique(Rows/Left/Tag, Rows/Left/Tag, Missing)", .invalidEntity),
  ("RepetitionNotUnique(Rows/Left/Tag, Rows/Left/Tag @From Missing)", .invalidEntity),
  ("RepetitionNotUnique(Rows/Left/Tag @From Rows/Left/Tag)", .noFieldsAllowed)]

example : siblingRefusals.all (fun (condition, expected) =>
    siblingAdmission condition == some expected.kernelCode) = true := by native_decide

example : ["RepetitionNotUnique(Rows/Left/Tag)",
    "RepetitionNotUnique(Rows/Left/Tag @From Rows)",
    "RepetitionNotUnique(Rows/Left/Tag, Rows/Right/N)",
    "RepetitionNotUnique(Rows/Right/N, Rows/Left/Tag)",
    "RepetitionNotUnique(Rows/Left/Tag, Rows/Right/N @From Rows)",
    "RepetitionNotUnique(Rows/Right/N, Rows/Left/Tag @From Rows)"].all (fun condition =>
      siblingAdmission condition == none) = true := by native_decide

private def keyRows (rows : List (Nat × String × Option Rat)) : DocumentData := {
  instantiatedRows := rows.map fun (row, _, _) => { group := 10, path := [row] }
  cells := rows.flatMap fun (row, tag, n) =>
    { address := { field := 3, path := [row] }, stored := tag, raw := .parsed (.str tag) } ::
      n.toList.map fun n => { address := { field := 4, path := [row] }, stored := toString n, raw := .parsed (.num n) } }

/-- Each firing row's `referenced` and `fillToFix` sets, rendered and sorted. -/
private def references (condition : String) (data : DocumentData) :
    Option (List (List Nat × List String × List String)) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Duplicates", errorCode := "DUPLICATES"
    errorEntityRelPath := "/Form/Rows/Tag", condition, severity := "ERROR" }).toOption
  let (_, results) ← (rule.fullRowsAndRepetitionResults document).toOption
  let base ← (document.applyFullIndexPreliminary.toOption.bind (·.messageReferenceInputs.toOption))
  let inputs := { base with repetitionAt := some fun environment => results.find? (·.row == environment) }
  let fired ← (runRuleAt world document rule).toOption
  let sorted (pointers : List MessagePointer) :=
    (pointers.map (renderFieldPointer model)).eraseDups.mergeSort (compare · · != .gt)
  fired.mapM fun (environment, message) => do
    let found ← (rule.condition.core.messageReferences message environment (some inputs)).toOption
    pure (environment.map (·.2), sorted found.referenced, sorted found.fillToFix)

/- A firing RNU leaf refers to its key at every duplicate row, while a non-firing one refers to
   nothing although a sibling fires the message (row 2 below, the Kernel's `missing-child` row of
   the validation-iteration-domain capture). A VALUE firing fills nothing; an OMISSION firing's
   fill-to-fix set is the whole duplicate cluster's keys (spec/07). -/
example :
    references (repeated ++ " Or FieldFilled(/Form/Rows/N)")
        (keyRows [(1, "same", some 2), (2, "other", some 5), (3, "same", some 7)]) =
      some [([1], ["Form/Rows/N", "Form/Rows/Tag", "Form/Rows[3]/Tag"], []),
        ([2], ["Form/Rows[2]/N"], []),
        ([3], ["Form/Rows/Tag", "Form/Rows[3]/N", "Form/Rows[3]/Tag"], [])] ∧
    references "RepetitionNotUnique(/Form/Rows/Tag, /Form/Rows/N @From /Form/Rows)"
        (keyRows [(1, "same", none), (2, "same", none)]) =
      some [([1], ["Form/Rows/N", "Form/Rows/Tag", "Form/Rows[2]/N", "Form/Rows[2]/Tag"],
          ["Form/Rows/N", "Form/Rows/Tag", "Form/Rows[2]/N", "Form/Rows[2]/Tag"]),
        ([2], ["Form/Rows/N", "Form/Rows/Tag", "Form/Rows[2]/N", "Form/Rows[2]/Tag"],
          ["Form/Rows/N", "Form/Rows/Tag", "Form/Rows[2]/N", "Form/Rows[2]/Tag"])] := by
  native_decide

end A12Kernel.Dm.RepetitionNotUniqueLocks
