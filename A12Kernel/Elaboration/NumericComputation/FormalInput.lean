import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.AddressedNumberFirstFilledComputation
import A12Kernel.Elaboration.NumericComputation.RunResult

/-! # Checked numeric-computation formal inputs -/

namespace A12Kernel

/-- One completed checked Number run paired with its call-global raw formal-input inventory. The numeric result keeps its exact target identity and independently rendered target messages. -/
structure NumericComputationFormalInputRunView (model : FlatModel)
    (Target : Type := FieldId) where
  private mk ::
  numeric : NumericComputationRunView (ComputationFormalMessage Unit) Target
  formalErrorsInOperands : List ComputationFormalInputFinding

namespace NumericComputationFormalInputRunView

/-- Construct the shared whole-call view after a family-owned execution has preserved its own target identity. -/
def of (numeric : NumericComputationRunView
    (ComputationFormalMessage Unit) Target)
    (formalErrorsInOperands : List ComputationFormalInputFinding) :
    NumericComputationFormalInputRunView model Target := {
  numeric
  formalErrorsInOperands
}

end NumericComputationFormalInputRunView

/-- Failure while composing the checked scalar run's direct-field inventory with execution and source-relative result projection. Once planning succeeds, an execution failure retains the exact eager raw findings even though no numeric result exists. -/
inductive NumericComputationFormalInputRunFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : NumericComputationRunResultFault)
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

/-- Check the call-global inventory before execution, then retain its raw findings on either execution arm without copying them into the rendered numeric message channel. -/
def executeResultWithFormalInputs (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model) :
    Except NumericComputationFormalInputRunFault
      (NumericComputationFormalInputRunView model) := do
  let inputPlan ← run.formalInputPlan |>.mapError .formalInput
  let findings := inputPlan.findings input
  match run.executeResult world input (fun _ => ()) [] with
  | .error cause => .error (.execution findings cause)
  | .ok numeric =>
      .ok (NumericComputationFormalInputRunView.of numeric findings)

end CheckedNumericComputationRun

/-- Failure while composing selected formal-input preparation with addressed Number `FirstFilledValue`. -/
inductive AddressedNumberFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedNumberFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedNumberFirstFilledComputation

/-- Bind every authored sibling-star source and the computed Number target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.sourceFields
    [operation.targetField]

/-- Prepare every selected source once, execute through that exact view, and retain raw findings beside rather than inside the typed Number result channels. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedNumberFirstFilledCheckedResultFault
      (NumericComputationFormalInputRunView model CellAddr) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation (fun _ => ()) [] with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result =>
      .ok (NumericComputationFormalInputRunView.of result.numeric
        prepared.formalErrorsInOperands)

end CheckedAddressedNumberFirstFilledComputation

end A12Kernel
