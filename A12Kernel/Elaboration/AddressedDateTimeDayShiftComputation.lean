import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.DateTimeDayShiftEvaluation
import A12Kernel.Elaboration.AddressedRepeatableTarget

/-! # Exact-address repeatable DateTime calendar-day shifts

This capsule binds the established model-zone calendar-day landing to one carrier-neutral repeatable target. The complete-DateTime source may be at the target scope or an enclosing scope, while the direct Number amount reads in the target environment. Result classification and separate-destination application remain with the common DateTime owners.
-/

namespace A12Kernel

inductive AddressedDateTimeDayShiftComputationElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetPolicy (cause : DateTimeTargetElabError)
  | source (cause : BoundCompleteDateTimeSourceElabError)
  | amount (cause : ValueAsDateTimeExtractionElabError)
  | unsupportedZone (zoneId : String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable complete-DateTime target, complete-DateTime source, and addressed Number amount certified by the same model. -/
structure CheckedAddressedDateTimeDayShiftComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  targetPolicy : CheckedDateTimeTarget model
  source : CheckedBoundCompleteDateTimeSource model checkedTarget.declaringGroup
    checkedTarget.declaration.repeatableScope
  profile : ModelZone.ConcreteProfile
  profileMatches :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some profile
  amount : CheckedTemporalShiftAmount model
  targetNotReferenced :
    (source.source.id == checkedTarget.targetField ||
      amount.referencesField checkedTarget.targetField) = false

/-- Check exact target placement and DateTime policy, bind both operands to its reading scope, and exclude target self-reference. -/
def checkAddressedDateTimeDayShiftComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath)
    (amountReference : SurfaceFieldPath) :
    Except AddressedDateTimeDayShiftComputationElabError
      (CheckedAddressedDateTimeDayShiftComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let targetPolicy ← elaborateDateTimeTargetIn model
    checkedTarget.declaration.repeatableScope checkedTarget.targetField
      |>.mapError .targetPolicy
  let source ← checkBoundCompleteDateTimeSource model checkedTarget.declaringGroup
    checkedTarget.declaration.path checkedTarget.declaration.repeatableScope
    sourceReference |>.mapError .source
  match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | none => throw (.unsupportedZone model.timeZoneId)
  | some profile =>
      let checkedAmount ←
        elaborateValueAsDateTimeRepeatableExpressionShiftAmount
          model checkedTarget.declaringGroup
          (.atom (.field amountReference)) |>.mapError .amount
      if hReference :
          source.source.id == checkedTarget.targetField ||
            checkedAmount.referencesField checkedTarget.targetField then
        throw (.targetSelfReference checkedTarget.targetField)
      else
        pure {
          checkedTarget
          targetPolicy
          source
          profile
          profileMatches := hProfile
          amount := checkedAmount
          targetNotReferenced := by simpa using hReference
        }

inductive AddressedDateTimeDayShiftComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | document (cause : CheckedDocumentError)
  | amountAddressing (cause : CheckedAddressingError)
  | dayShift (cause : DateTimeDayShiftFault)
  | target (cause : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One exact source/target-address pair and its declaration-rendered DateTime outcome. -/
structure AddressedDateTimeDayShiftComputationOutcome where
  sourceField : CellAddr
  targetField : CellAddr
  outcome : DateTimeTargetOutcome
  deriving Repr, DecidableEq

/-- One model-indexed addressed calendar-day result retaining the checked operation for exact application. -/
structure AddressedDateTimeDayShiftComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedDateTimeDayShiftComputation model
  dateTime : DateTimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedDateTimeDayShiftComputation

def referencesField
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (field : FieldId) : Bool :=
  operation.source.source.id == field || operation.amount.referencesField field

def fieldDependencies
    (operation : CheckedAddressedDateTimeDayShiftComputation model) :
    List FieldId :=
  operation.source.source.id :: operation.amount.fieldDependencies

private def classifyAt
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (environment : Env) (sourceField : CellAddr)
    (result : ValueAsDateTimeResult) :
    Except AddressedDateTimeDayShiftComputationFault
      AddressedDateTimeDayShiftComputationOutcome := do
  let targetPath ← environment.pathForScope
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .environment
  let outcome ← operation.targetPolicy.evaluate
    result.asTemporalComputationResult |>.mapError .target
  pure {
    sourceField
    targetField := {
      field := operation.checkedTarget.targetField
      path := targetPath
    }
    outcome
  }

private def evaluateAt
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedDateTimeDayShiftComputationFault
      AddressedDateTimeDayShiftComputationOutcome := do
  let sourcePath ← environment.pathForScope
    operation.source.sourceDeclaration.repeatableScope
      |>.mapError .environment
  let sourceField : CellAddr := {
    field := operation.source.source.id
    path := sourcePath
  }
  let sourceCell ← input.read sourceField |>.mapError .document
  let result ← CheckedDateTimeDayShift.evaluateObservation
    operation.profile operation.source.source.id
    (observeCell .computation sourceCell)
    (fun _ => operation.amount.readAddressed .computation {
      scalar := {
        fields := input.flatContext
        groups := GroupPresenceContext.unavailable
      }
      outer := environment
      input := .checked input
    } |>.mapError .amountAddressing)
    (fun cause => .dayShift cause)
  operation.classifyAt environment sourceField result

/-- Execute once per physically instantiated target row in document order. -/
def execute
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateTimeDayShiftComputationFault
      (List AddressedDateTimeDayShiftComputationOutcome) := do
  let environments ← input.actualRowEnvironments
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAt input)

/-- Classify already-executed exact row outcomes against immutable source target state. -/
def resultFromOutcomes
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedDateTimeDayShiftComputationOutcome) :
    AddressedDateTimeDayShiftComputationRunView model ResidualMessage := {
  operation
  dateTime := DateTimeComputationRunView.fromOutcomesAt
    input.sourceDateTimeTargetStateAt residualMessages
    (outcomes.map fun entry => (entry.targetField, entry.outcome))
}

/-- Execute and classify exact row outcomes through the common DateTime result owner. -/
def executeResult
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedDateTimeDayShiftComputationFault
      (AddressedDateTimeDayShiftComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure (operation.resultFromOutcomes input residualMessages outcomes)

end CheckedAddressedDateTimeDayShiftComputation

namespace AddressedDateTimeDayShiftComputationRunView

/-- Apply only retained exact-address DateTime actions to a separate checked destination of the same model. -/
def applyToChecked
    (view : AddressedDateTimeDayShiftComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (DateTimeComputationRunView.DateTimeComputationRunApplicationError
      CellAddr) (DateTimeComputationDestination CellAddr) :=
  view.dateTime.applyTo destination.sourceDateTimeTargetStateAt

end AddressedDateTimeDayShiftComputationRunView

end A12Kernel
