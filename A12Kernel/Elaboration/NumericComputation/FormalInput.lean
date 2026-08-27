import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.NumericComputation.RunPlan

/-! # Checked numeric-computation formal inputs -/

namespace A12Kernel

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

end A12Kernel
