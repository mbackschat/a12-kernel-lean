import A12Kernel.Elaboration.TimeFromDateTimeComputation

/-! # Exact-address repeatable `TimeFromDateTime`

This capsule specializes the checked repeatable placement and physical target-row environment to the existing wall-clock extractor, Time target, exact-key result channels, and Time application fold. It retains source and target addresses without reconstructing a document or claiming scheduler, validation, or pointer-rendering behavior.
-/

namespace A12Kernel

inductive AddressedTimeFromDateTimeElabError where
  | targetLookup (cause : ResolveError)
  | target (cause : TimeTargetElabError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | source (cause : BoundCompleteDateTimeSourceElabError)
  deriving Repr, DecidableEq

/-- One exact repeatable Time extraction certified against a validated model. -/
structure CheckedAddressedTimeFromDateTime (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  target : CheckedTimeTarget model
  sourceBinding : CheckedBoundCompleteDateTimeSource model declaringGroup
    target.checked.declaration.repeatableScope
  targetInDeclaringGroup :
    target.checked.declaration.groupPath = declaringGroup
  targetRepeatable : target.checked.declaration.repeatableScope ≠ []

/-- Certify one complete-DateTime source whose repeatable levels the Time target's own scope binds. -/
def checkAddressedTimeFromDateTime
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedTimeFromDateTimeElabError
      (CheckedAddressedTimeFromDateTime model) := do
  let targetDeclaration ← model.lookupUniqueId targetField |>.mapError .targetLookup
  let checkedTarget ←
    elaborateTemporalTargetPolicyIn model targetDeclaration.repeatableScope targetField
      |>.mapError (fun cause => .target (.targetPolicy cause))
  let target ← checkedTarget.toTimeTarget |>.mapError .target
  if hGroup : target.checked.declaration.groupPath = declaringGroup then
    if hRepeatable : target.checked.declaration.repeatableScope.isEmpty then
      throw (.targetNotRepeatable target.checked.declaration.path)
    else
      let sourceBinding ← checkBoundCompleteDateTimeSource model declaringGroup
        target.checked.declaration.path
        target.checked.declaration.repeatableScope sourceReference
        |>.mapError .source
      pure {
        declaringGroup, target, sourceBinding
        targetInDeclaringGroup := hGroup
        targetRepeatable := by
          intro empty
          simp [empty] at hRepeatable
      }
  else
    throw (.targetOutsideDeclaringGroup
      target.checked.declaration.path declaringGroup)

inductive AddressedTimeFromDateTimeFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | source (cause : ValueAsDateTimeExtractionFault)
  deriving Repr, DecidableEq

/-- One row-local Time outcome with the exact source and target addresses needed by Execute and Explain consumers. -/
structure AddressedTimeFromDateTimeOutcome where
  sourceField : CellAddr
  targetField : CellAddr
  outcome : TimeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked addressed Time result backed by the common Time channels over exact cell addresses. -/
structure AddressedTimeFromDateTimeRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedTimeFromDateTime model
  time : TimeComputationRunView ResidualMessage CellAddr

namespace AddressedTimeFromDateTimeRunView

private def fromOutcomes (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedTimeFromDateTimeOutcome) :
    AddressedTimeFromDateTimeRunView model ResidualMessage := {
  operation
  time := TimeComputationRunView.fromOutcomesAt
    input.sourceTimeTargetStateAt residualMessages
    (outcomes.map fun entry => (entry.targetField, entry.outcome))
}

end AddressedTimeFromDateTimeRunView

namespace CheckedAddressedTimeFromDateTime

private def evaluateAtEnvironment
    (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeFromDateTimeFault
      AddressedTimeFromDateTimeOutcome := do
  let sourcePath ←
    (environment.pathForScope
      operation.sourceBinding.sourceDeclaration.repeatableScope)
      |>.mapError .environment
  let targetPath ←
    (environment.pathForScope operation.target.checked.declaration.repeatableScope)
      |>.mapError .environment
  let sourceAddress : CellAddr := {
    field := operation.sourceBinding.source.id, path := sourcePath
  }
  let targetAddress : CellAddr := {
    field := operation.target.checked.target.id, path := targetPath
  }
  let operand ← readTimeFromDateTimeSourceAt operation.sourceBinding.source
    sourceAddress .computation input |>.mapError .source
  let outcome := operation.target.evaluate operand.asTimeComputationResult
  pure { sourceField := sourceAddress, targetField := targetAddress, outcome }

/-- Execute once per physically instantiated target row in document order. -/
def execute (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedTimeFromDateTimeFault
      (List AddressedTimeFromDateTimeOutcome) := do
  let environments ←
    input.actualRowEnvironments operation.target.checked.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAtEnvironment input)

/-- Execute every physical target row and classify each rich Time outcome against immutable source state at that exact target address. -/
def executeResult (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except AddressedTimeFromDateTimeFault
      (AddressedTimeFromDateTimeRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure (AddressedTimeFromDateTimeRunView.fromOutcomes operation input
    residualMessages outcomes)

end CheckedAddressedTimeFromDateTime

namespace AddressedTimeFromDateTimeRunView

/-- Apply retained source-relative Time actions to exact cell-state projections from a separately supplied checked document of the same model. -/
def applyToChecked
    (view : AddressedTimeFromDateTimeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (TemporalValueComputationApplicationError CellAddr)
      (TimeComputationDestination CellAddr) :=
  view.time.applyTo destination.sourceTimeTargetStateAt

end AddressedTimeFromDateTimeRunView

end A12Kernel
