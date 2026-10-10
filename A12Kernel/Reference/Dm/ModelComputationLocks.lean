import A12Kernel.Reference.Dm.ModelComputation

namespace A12Kernel.Dm.ModelComputationLocks

open A12Kernel

private def computation (name target operation : String) : DmComputation := {
  group := ["Form"], name, targetRelPath := "../" ++ target
  commonPrecondition := none
  alternatives := [{ precondition := none, operation }]
  errorCodesToSuppress := [] }

private def model (producerOperation : String) (extraAlternative := false) : DmModel := {
  flat := { fields := [
    { id := 1, groupPath := ["Form"], name := "Producer"
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form"], name := "Consumer"
      policy := { kind := .number { scale := 0, signed := true } } }] }
  rules := [], conditionLanguage := "en_US", refusals := []
  computations := [computation "Read" "Consumer" "[Producer]",
    computation "Write" "Producer" producerOperation] ++
      if extraAlternative then [computation "OtherWrite" "Producer" "UnknownFunction(1)"] else [] }

private def run (producerOperation : String) (extraAlternative := false) :
    Option (Bool × List String) := do
  let dm := model producerOperation extraAlternative
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [{ address := { field := 1, path := [] }, stored := "90", raw := .parsed (.num 90) }] }).toOption
  pure (match runModelComputations dm .english world prepared checked with
    | .ok values => (true, values.map (·.outcome))
    | .error _ => (false, []))

example : run "7" = some (true, ["value 7", "value 7"]) := by native_decide

example : run "UnknownFunction(1)" = some (false, []) := by native_decide

example : run "7" true = some (false, []) := by native_decide

private def refusalBoundary (refused : Bool) : Option Bool := do
  let dm := { model "7" with
    refusals := if refused then [(["Form", "Other"], "unsupported declaration")] else [] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
  pure (runModelComputations dm .english world prepared checked).isOk

example : refusalBoundary false = some true ∧ refusalBoundary true = some false := by
  native_decide

end A12Kernel.Dm.ModelComputationLocks
