import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Elaboration.NumericComputation.FormalInput

/-! # Generated numeric-table formal-input composition

This boundary projects every guard and checked operation into one target-excluding input plan, prepares the selected preliminary once, and executes the generated table through that exact view. Generated-table admission, first selection, addressed operation evaluation, target completion, and Number result classification remain with their existing owners.
-/

namespace A12Kernel

/-- Failure while reusing generated-table admission before binding its complete direct-field inventory. -/
inductive GeneratedNumericComputationFormalInputPlanError where
  | validation (cause : GeneratedComputationValidationError)
  | formalInput (cause : ComputationFormalInputPlanError)
  deriving Repr, DecidableEq

/-- Failure while composing one generated numeric table's admitted static inventory with its exact-address public result. Planning and preparation failures do not expose findings; post-preparation execution failures retain them. -/
inductive GeneratedNumericComputationFormalInputRunError where
  | validation (cause : GeneratedComputationValidationError)
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : GeneratedNumericComputationRunResultError)
  deriving Repr

private def optionalGeneratedGuardReferences
    (guard : Option ComputationCondition) (field : FieldId) : Bool :=
  match guard with
  | none => false
  | some condition => condition.referencesField field

private def generatedNumericOperationReferences
    (operation : CheckedNumericComputationOperation model)
    (field : FieldId) : Bool :=
  operation.core.expression.anyAtom
    (CheckedNumericComputationAtom.references model field)

private def generatedNumericAlternativeReferences
    (alternative : GeneratedComputationAlternative
      (CheckedNumericComputationOperation model))
    (field : FieldId) : Bool :=
  alternative.precondition.referencesField field ||
    generatedNumericOperationReferences alternative.operation field

private def generatedNumericAlternativesReference
    (alternatives : GeneratedComputationAlternatives
      (CheckedNumericComputationOperation model))
    (field : FieldId) : Bool :=
  match alternatives with
  | .singleton alternative =>
      optionalGeneratedGuardReferences alternative.precondition field ||
        generatedNumericOperationReferences alternative.operation field
  | .guarded guarded =>
      guarded.declaredAlternatives.any fun alternative =>
        generatedNumericAlternativeReferences alternative field

namespace GeneratedComputationTable

/-- Whether the common guard, any alternative guard, or any complete checked operation references one field. -/
def referencesField (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model)) (field : FieldId) : Bool :=
  optionalGeneratedGuardReferences computation.commonPrecondition field ||
    generatedNumericAlternativesReference computation.alternatives field

/-- Enumerate every validated model declaration referenced anywhere in the generated numeric table. -/
def fieldDependencies (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model)) : List FieldId :=
  (model.fields.filter fun declaration =>
    computation.referencesField declaration.id).map fun declaration =>
      declaration.id

end GeneratedComputationTable

namespace AdmittedGeneratedNumericOperationTable

/-- Bind the already-admitted generated table's complete dependency union to the shared target-excluding inventory without repeating generated validation admission. -/
def formalInputPlan
    (_admission : AdmittedGeneratedNumericOperationTable model computation) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model computation.fieldDependencies
    [computation.targetField]

end AdmittedGeneratedNumericOperationTable

namespace GeneratedComputationTable

/-- Admit the generated-validation shell first, then bind its complete common, row-guard, and checked-operation dependency union to the shared target-excluding formal-input plan. -/
def formalInputPlan (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model)) :
    Except GeneratedNumericComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) := do
  let admission ← admitGeneratedNumericOperationTable model computation
    |>.mapError .validation
  admission.formalInputPlan |>.mapError .formalInput

/-- Admit one generated table once, prepare its selected noncomputed inputs, execute scalar guards and the selected operation through that view, and retain the eager findings beside either its exact-address Number result or any subsequent execution failure. -/
def executeNumericResultWithFormalInputs (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model))
    (world : World) (input : CheckedDocument model) :
    Except GeneratedNumericComputationFormalInputRunError
      (NumericComputationFormalInputRunView model CellAddr) := do
  let admission ← admitGeneratedNumericOperationTable model computation
    |>.mapError .validation
  let inputPlan ← admission.formalInputPlan |>.mapError .formalInput
  let prepared ← inputPlan.prepare input |>.mapError .preliminary
  match admission.executeAddressedResultWithRead world input
      prepared.preliminary.readComputation (fun _ => ()) [] with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok numeric =>
      .ok (NumericComputationFormalInputRunView.of numeric
        prepared.formalErrorsInOperands)

end GeneratedComputationTable

end A12Kernel
