import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Replay

/-! # Computation guard context locks

The checked guard needs the current addressed overlay on both mixed scheduled runs and standalone
run policies; rebuilding only its scalar read loses the expanded field-fill operands.
-/

namespace A12Kernel.Dm.ComputationGuardLocks

open A12Kernel A12Kernel.Dm

private def fillGuardFreshRun (repeated : Bool) (stringTarget : Bool := false)
    (legacy : Bool := false) : Option (List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form", "Inputs"]
  let model : FlatModel := {
    fields := [
      { id := 1, groupPath := group, name := "Value", policy := { kind := .number { scale := 0, signed := true } }
        repeatableScope := if repeated then [10] else [] },
      { id := 2, groupPath := ["Form"], name := "Out", policy := {
        kind := if stringTarget then .string else .number { scale := 0, signed := true } } }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input : DocumentData := {
    instantiatedRows := if repeated then [{ group := 10, path := [1] }, { group := 10, path := [2] }] else []
    cells := (if repeated then [[1], [2]] else [[]]).map fun path =>
      { address := { field := 1, path }, stored := if legacy then "1" else "bad"
        raw := if legacy then .parsed (.num 1) else .rejected .malformed } }
  let checked ← (checkDocument prepared "en_US" input).toOption
  let producer : DmComputation := {
    group := ["Form"], name := "Producer", targetRelPath := if repeated then "../Rows/Value" else "../Inputs/Value"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
  let consumer : DmComputation := {
    group := ["Form"], name := "Consumer", targetRelPath := "../Out"
    commonPrecondition := some (if repeated then "AllFieldsFilled(Rows*)" else "AllFieldsFilled(Inputs)")
    alternatives := [{ precondition := none, operation := if stringTarget then "\"fresh\"" else "2" }], errorCodesToSuppress := [] }
  let guardText := consumer.commonPrecondition.getD ""
  let (_, producer) ← (lowerComputation model .english producer).toOption
  let (_, consumer) ← (lowerComputation model .english consumer).toOption
  if legacy then
    let parsed ← (parseText .english guardText).toOption
    let surface ← (lowerGuard model ["Form"] false parsed.body).toOption
    let guard ← (model.elaborateComputationCondition ["Form"] ["Form"] surface).toOption
    let context ← match consumer with
      | .number table _ => do
          let run ← (certifyNumericComputationRun [table]).toOption
          pure (run.readPolicy {} checked)
      | .string table => do
          let run ← (certifyStringComputationRun [table]).toOption
          pure (run.readPolicy {} checked)
      | _ => none
    return if (guard.evalChecked context).toOption == some .holds then ["holds"] else ["other"]
  let outcomes ← (runComputations world prepared checked [consumer, producer]).toOption
  pure (outcomes.map (·.outcome))

example : fillGuardFreshRun false = some ["value 1", "value 2"] ∧
    fillGuardFreshRun true = some ["value 1", "value 1", "value 2"] := by native_decide

example : fillGuardFreshRun false true = some ["value 1", "value fresh"] := by native_decide
example : fillGuardFreshRun true true = some ["value 1", "value 1", "value fresh"] := by native_decide
example : fillGuardFreshRun true false true = some ["holds"] := by native_decide
example : fillGuardFreshRun true true true = some ["holds"] := by native_decide


end A12Kernel.Dm.ComputationGuardLocks
