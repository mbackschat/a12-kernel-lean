import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Checked formal inputs for finite mixed scalar runs

This boundary builds one target-excluding eager inventory from every typed String and Number step, then retains that inventory beside either the family-partitioned result or the exact typed execution/result fault.
-/

namespace A12Kernel

/-- One successful mixed scalar result paired with its call-global raw formal-input inventory. -/
structure ScalarComputationFormalInputRunView (model : FlatModel)
    (StringResidual NumberPayload : Type) where
  private mk ::
  scalar : ScalarComputationRunView StringResidual NumberPayload
  formalErrorsInOperands : List ComputationFormalInputFinding

namespace ScalarComputationFormalInputRunView

def of (scalar : ScalarComputationRunView StringResidual NumberPayload)
    (formalErrorsInOperands : List ComputationFormalInputFinding) :
    ScalarComputationFormalInputRunView model StringResidual NumberPayload := {
  scalar
  formalErrorsInOperands
}

end ScalarComputationFormalInputRunView

/-- Failure while composing the mixed run's complete direct-field inventory with execution and source-relative result projection. -/
inductive ScalarComputationFormalInputRunFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : ScalarComputationRunResultFault)
  deriving Repr, DecidableEq

namespace CheckedScalarComputationRun

/-- Project every checked typed step to the shared `(target, raw dependencies)` whole-call shape in certified execution order. -/
def formalInputOperations (run : CheckedScalarComputationRun model) :
    List (FieldId × List FieldId) :=
  run.steps.map fun step => (step.targetField, step.fieldDependencies)

/-- Build one call-global target-excluding input plan across both scalar families. -/
def formalInputPlan (run : CheckedScalarComputationRun model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputOperations model run.formalInputOperations

/-- Collect the complete eager mixed inventory before execution, then retain it beside either the exact family-partitioned result or the exact typed failure. -/
def executeResultWithFormalInputs
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual) :
    Except ScalarComputationFormalInputRunFault
      (ScalarComputationFormalInputRunView model
        StringResidual NumberPayload) := do
  let plan ← run.formalInputPlan |>.mapError .formalInput
  let findings := plan.findings input
  match run.executeResult world patterns input numberPayloadAt
      numberMessages stringResidualMessages with
  | .error cause => .error (.execution findings cause)
  | .ok result => .ok (ScalarComputationFormalInputRunView.of result findings)

end CheckedScalarComputationRun

end A12Kernel
