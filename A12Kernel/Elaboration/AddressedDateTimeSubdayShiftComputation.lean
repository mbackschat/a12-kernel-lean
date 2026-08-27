import A12Kernel.Elaboration.DateTimeSubdayShiftComputation
import A12Kernel.Elaboration.AddressedRepeatableTarget

/-! # Exact-address repeatable DateTime sub-day shifts

This capsule binds the existing exact-instant DateTime shift to one carrier-neutral repeatable target. Source and amount scopes come from the target environment, while result classification and separate-destination application remain with the established DateTime owners.
-/

namespace A12Kernel

inductive AddressedDateTimeSubdayShiftComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetPolicy (cause : DateTimeTargetElabError)
  | shift (cause : AddressedDateTimeShiftElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable complete-DateTime target and one exact addressed sub-day shift certified by the same model. -/
structure CheckedAddressedDateTimeSubdayShiftComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  targetPolicy : CheckedDateTimeTarget model
  shift : CheckedAddressedDateTimeShift model checkedTarget.declaringGroup
    checkedTarget.declaration.repeatableScope
  targetNotReferenced :
    shift.referencesField checkedTarget.targetField = false

/-- Check target placement and profile before certifying the source-first addressed shift and excluding target self-reference. -/
def checkAddressedDateTimeSubdayShiftComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) (unit : DateTimeSubdayUnit)
    (amount : AuthoredNumericExpr SurfaceNumericAtom) :
    Except AddressedDateTimeSubdayShiftComputationElabError
      (CheckedAddressedDateTimeSubdayShiftComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let targetPolicy ← elaborateDateTimeTargetIn model
    checkedTarget.declaration.repeatableScope checkedTarget.targetField
      |>.mapError .targetPolicy
  let shift ← elaborateAddressedDateTimeShift model checkedTarget.declaringGroup
    checkedTarget.declaration.path checkedTarget.declaration.repeatableScope
    sourceReference unit amount |>.mapError .shift
  if hReference : shift.referencesField checkedTarget.targetField then
    throw (.targetSelfReference checkedTarget.targetField)
  else
    pure {
      checkedTarget
      targetPolicy
      shift
      targetNotReferenced := by simpa using hReference
    }

inductive AddressedDateTimeSubdayShiftComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | shift (cause : AddressedDateTimeShiftFault)
  | target (cause : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One exact source/target-address pair and its declaration-rendered DateTime outcome. -/
structure AddressedDateTimeSubdayShiftComputationOutcome where
  sourceField : CellAddr
  targetField : CellAddr
  outcome : DateTimeTargetOutcome
  deriving Repr, DecidableEq

/-- One model-indexed addressed DateTime result retaining the checked operation for exact application. -/
structure AddressedDateTimeSubdayShiftComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedDateTimeSubdayShiftComputation model
  dateTime : DateTimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedDateTimeSubdayShiftComputation

def fieldDependencies
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model) :
    List FieldId :=
  operation.shift.fieldDependencies

def referencesField
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (field : FieldId) : Bool :=
  operation.shift.referencesField field

private def classifyAt
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (environment : Env) (shifted : AddressedDateTimeShiftEvaluation) :
    Except AddressedDateTimeSubdayShiftComputationFault
      AddressedDateTimeSubdayShiftComputationOutcome := do
  let targetPath ← environment.pathForScope
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetEnvironment
  let outcome ← operation.targetPolicy.evaluate
    shifted.result.asTemporalComputationResult |>.mapError .target
  pure {
    sourceField := shifted.sourceField
    targetField := {
      field := operation.checkedTarget.targetField
      path := targetPath
    }
    outcome
  }

private def evaluateAt
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedDateTimeSubdayShiftComputationFault
      AddressedDateTimeSubdayShiftComputationOutcome := do
  let shifted ← operation.shift.evaluateAt input environment |>.mapError .shift
  operation.classifyAt environment shifted

/-- Evaluate one exact target row with the immutable DateTime source and a caller-supplied addressed amount view. -/
def evaluateAtWithAmountRead
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (environment : Env)
    (amountRead : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell)) :
    Except AddressedDateTimeSubdayShiftComputationFault
      AddressedDateTimeSubdayShiftComputationOutcome := do
  let shifted ← operation.shift.evaluateAtWithAmountRead input environment amountRead
    |>.mapError .shift
  operation.classifyAt environment shifted

/-- Execute every physical target row while numeric amounts read through one transient addressed view. -/
def executeWithAmountRead
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model)
    (amountRead : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell)) :
    Except AddressedDateTimeSubdayShiftComputationFault
      (List AddressedDateTimeSubdayShiftComputationOutcome) := do
  let environments ← input.actualRowEnvironments
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM fun environment =>
    operation.evaluateAtWithAmountRead input environment amountRead

/-- Execute once per physically instantiated target row in document order. -/
def execute
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateTimeSubdayShiftComputationFault
      (List AddressedDateTimeSubdayShiftComputationOutcome) := do
  let environments ← input.actualRowEnvironments
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAt input)

/-- Classify already-executed exact row outcomes against immutable source target state. -/
def resultFromOutcomes
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedDateTimeSubdayShiftComputationOutcome) :
    AddressedDateTimeSubdayShiftComputationRunView model ResidualMessage := {
  operation
  dateTime := DateTimeComputationRunView.fromOutcomesAt
    input.sourceDateTimeTargetStateAt residualMessages
    (outcomes.map fun entry => (entry.targetField, entry.outcome))
}

/-- Classify exact row outcomes against immutable source target state through the common DateTime result owner. -/
def executeResult
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedDateTimeSubdayShiftComputationFault
      (AddressedDateTimeSubdayShiftComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure (operation.resultFromOutcomes input residualMessages outcomes)

end CheckedAddressedDateTimeSubdayShiftComputation

namespace AddressedDateTimeSubdayShiftComputationRunView

/-- Apply only retained exact-address DateTime actions to a separate checked destination of the same model. -/
def applyToChecked
    (view : AddressedDateTimeSubdayShiftComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (DateTimeComputationRunView.DateTimeComputationRunApplicationError
      CellAddr) (DateTimeComputationDestination CellAddr) :=
  view.dateTime.applyTo destination.sourceDateTimeTargetStateAt

end AddressedDateTimeSubdayShiftComputationRunView

end A12Kernel
