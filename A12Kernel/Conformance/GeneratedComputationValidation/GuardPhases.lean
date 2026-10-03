import A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

/-! # Computation guard and generated-validation phase separators -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.GuardPhases

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

/- Computation aborts on a reached invalid text guard; generated validation applies UNKNOWN Or TRUE
and still reports the target mismatch. This locks the phase boundary, not a Kernel capture claim. -/
example :
    (do
      let source := { model with fields := model.fields ++ [
        { textGuard with id := 7, name := "HealthyText" }] }
      let guard : ComputationCondition := .or
        (.leaf (.text (.string .equal { id := textGuard.id } "A")))
        (.leaf (.text (.string .equal { id := 7 } "A")))
      let candidate := singletonComputation (some guard) 3
      let raw : RawFlatContext := { read := fun field =>
        if field == target.id then .parsed (.num 1)
        else if field == textGuard.id then .rejected .malformed
        else if field == 7 then .parsed (.str "A") else .empty }
      let selected := GeneratedComputationTable.selectFirst candidate
        { read := (source.checkContext raw).read }
      let rule ← (assembleGeneratedLiteralNumberRule source candidate).toOption
      let outcome ← evalFlatRule? source rule raw true
      pure (selected, outcome)) =
        some (.poison .malformed, .fired (expectedMessage .value)) := by
  native_decide

end A12Kernel.Conformance.GeneratedComputationValidation.GuardPhases
