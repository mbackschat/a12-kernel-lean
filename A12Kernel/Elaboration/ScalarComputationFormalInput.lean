import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Checked formal inputs for finite mixed scalar runs

This boundary prepares one target-excluding eager inventory and index view from every typed String and Number step, then retains the cached and generated findings beside either the family-partitioned result or the exact typed execution/result fault.
-/

namespace A12Kernel

/-- One successful mixed scalar result paired with its prepared formal-input inventory. -/
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

/-- Failure while composing the mixed run's direct-field inventory with selected preliminary preparation, execution, and source-relative result projection. -/
inductive ScalarComputationFormalInputRunFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : ScalarComputationRunResultFault)
  | assembly (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : ComputationReportAssemblyFault)
  deriving Repr, DecidableEq

namespace CheckedScalarComputationRun

/-- Full Number diagnostic pointers before partitioning. Value-less Number errors have no computed instance, while payloadful rejections are represented by the supplied stream. -/
def numberReportPointers (outcomes : List ScalarComputationOutcome)
    (messages : List (ComputationFormalMessage NumberPayload)) : List MessagePointer :=
  messages.map (·.pointer) ++ outcomes.filterMap fun
    | .number target outcome =>
        if outcome.emitsValuelessTargetError then
          some (MessagePointer.ofCellAddr { field := target, path := [] }) else none
    | .string _ _ | .document _ _ => none

/-- Project every checked typed step to the shared `(target, raw dependencies)` whole-call shape in certified execution order. -/
def formalInputOperations (run : CheckedScalarComputationRun model) :
    List (FieldId × List FieldId) :=
  (analyzeScalarComputationSteps run.steps).map fun analysis =>
    (analysis.targetField, analysis.fieldDependencies)

/-- Build one call-global target-excluding input plan across both scalar families. -/
def formalInputPlan (run : CheckedScalarComputationRun model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputOperations model run.formalInputOperations

/-- Prepare selected index state, execute once through its staged cells, check the complete Number and operand report stream, then project against the immutable source. Opaque String residuals remain the caller's already-assembled channel. -/
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
  let prepared ← plan.prepare input |>.mapError .preliminary
  let findings := prepared.formalErrorsInOperands
  let outcomes ← (run.execute world patterns prepared.preliminary.computationInput)
    |>.mapError (fun cause => .execution findings (.execution cause))
  checkComputationReportPointers ((findings.map fun finding => MessagePointer.ofCellAddr finding.address) ++
    numberReportPointers outcomes numberMessages) |>.mapError (.assembly findings)
  let result ← (resultFromOutcomes input numberPayloadAt numberMessages stringResidualMessages outcomes)
    |>.mapError (.execution findings)
  pure (ScalarComputationFormalInputRunView.of result findings)

end CheckedScalarComputationRun

end A12Kernel
