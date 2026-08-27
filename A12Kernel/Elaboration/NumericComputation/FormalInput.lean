import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.NumericComputation.RunResult

/-! # Checked numeric-computation formal inputs -/

namespace A12Kernel

/-- One completed checked scalar Number run paired with its call-global raw formal-input inventory. The numeric result keeps its independently rendered target messages. -/
structure NumericComputationFormalInputRunView (model : FlatModel) where
  private mk ::
  numeric : NumericComputationRunView (ComputationFormalMessage Unit)
  formalErrorsInOperands : List ComputationFormalInputFinding

/-- Failure while composing the checked scalar run's direct-field inventory with execution and source-relative result projection. -/
inductive NumericComputationFormalInputRunFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (cause : NumericComputationRunResultFault)
  deriving Repr, DecidableEq

namespace CheckedNumericComputationOperation

/-- Enumerate every validated model field referenced by the checked expression. Filtering the model declaration inventory turns group-subtree reference predicates into concrete field dependencies without inventing group findings. -/
def fieldDependencies (operation : CheckedNumericComputationOperation model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    operation.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model declaration.id)).map
        (·.id)

/-- Bind one checked numeric operation's resolved field dependencies and computed target to the shared formal-input collector. -/
def formalInputPlan (operation : CheckedNumericComputationOperation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.core.target.id]

end CheckedNumericComputationOperation

namespace CheckedNumericComputationTable

/-- Enumerate the validated model fields referenced by every checked alternative guard and operation in the table. -/
def fieldDependencies (table : CheckedNumericComputationTable model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    table.referencesField declaration.id).map (·.id)

/-- Bind one complete checked numeric table's dependencies and shared target to the formal-input collector. -/
def formalInputPlan (table : CheckedNumericComputationTable model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model table.fieldDependencies
    [table.targetField]

end CheckedNumericComputationTable

namespace CheckedNumericComputationRun

/-- Project every certified table to the shared `(target, raw dependencies)` formal-input shape in checked run order. -/
def formalInputOperations (run : CheckedNumericComputationRun model) :
    List (FieldId × List FieldId) :=
  run.tables.map fun table => (table.targetField, table.fieldDependencies)

/-- Build one call-global formal-input plan from every table and every computed target in the checked scalar run. -/
def formalInputPlan (run : CheckedNumericComputationRun model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputOperations model run.formalInputOperations

/-- Check the call-global inventory before execution, then project its raw findings on success without copying them into the rendered numeric message channel. -/
def executeResultWithFormalInputs (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model) :
    Except NumericComputationFormalInputRunFault
      (NumericComputationFormalInputRunView model) := do
  let inputPlan ← run.formalInputPlan |>.mapError .formalInput
  let numeric ← run.executeResult world input (fun _ => ()) []
    |>.mapError .execution
  pure {
    numeric
    formalErrorsInOperands := inputPlan.findings input
  }

end CheckedNumericComputationRun

end A12Kernel
