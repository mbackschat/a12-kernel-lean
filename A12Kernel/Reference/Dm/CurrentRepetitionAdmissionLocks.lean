import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.CurrentRepetitionAdmissionLocks

private def number (id : FieldId) (groupPath : GroupPath) (repeatableScope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, groupPath, repeatableScope, name := "Amount", policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [{ number 1 ["Form"] with name := "Total" }, number 2 ["Form", "Fixed"],
    number 3 ["Form", "Repeating"] [10]]
  repeatableGroups := [{ level := 10, path := ["Form", "Repeating"], repeatability := some 3 }] }

private def admission (path : String) (filter : Bool) : Option String :=
  let comparison := "CurrentRepetition(" ++ path ++ ") > 0"
  let condition := if filter then "Sum(Repeating*/Amount Having " ++ comparison ++ ") > 0" else comparison
  match checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      group := ["Form"], name := "Repetition", errorCode := "REPETITION", errorEntityRelPath := "../Total",
      condition := "FieldFilled(Total) And " ++ condition, severity := "ERROR" } with
  | .ok _ => none
  | .error refusal => some refusal.detail

private def expected (segment : String) (starred field filter : Bool) : Option KernelStaticDiagnostic :=
  if segment == "Missing" then some .invalidEntity
  else if starred && segment == "Fixed" then some .invalidWildcard
  else if segment == "Repeating" && !starred && !filter then some .noWildcard
  else if field then some .noFieldsAllowed
  else if starred then some .noWildcardsAllowed
  else if filter && segment == "Fixed" then some .noIterationForWildcard
  else none

example : model.validate.isOk = true := by native_decide

-- PathGatePopulation.repetitionRows at e975b4258 separates resolution, star placement and
-- operator-kind refusals before filter binding; its accepted twins guard against generic refusal.
example : [false, true].all (fun filter => ["Missing", "Fixed", "Repeating"].all fun segment =>
    [false, true].all fun starred => [false, true].all fun field =>
      let path := segment ++ (if starred then "*" else "") ++ (if field then "/Amount" else "")
      admission path filter == (expected segment starred field filter).map (·.kernelCode)) = true := by native_decide

end A12Kernel.Dm.CurrentRepetitionAdmissionLocks
