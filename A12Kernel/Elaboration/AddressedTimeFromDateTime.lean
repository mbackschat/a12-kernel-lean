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
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetContainedInDeclaringGroup :
    GroupPath.isPrefixOf declaringGroup target.checked.declaration.groupPath = true
  targetRepeatable : target.checked.declaration.repeatableScope ≠ []

/-- Certify one complete-DateTime source whose repeatable levels the Time target's own scope binds. -/
def checkAddressedTimeFromDateTime
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedTimeFromDateTimeElabError
      (CheckedAddressedTimeFromDateTime model) := do
  let targetDeclaration ← model.lookupUniqueId targetField |>.mapError .targetLookup
  let target ← elaborateTimeTargetIn model
      targetDeclaration.repeatableScope targetField
    |>.mapError .target
  if hValid : GroupPath.isValid declaringGroup = true then
    if hGroup : GroupPath.isPrefixOf
        declaringGroup target.checked.declaration.groupPath = true then
      if hRepeatable : target.checked.declaration.repeatableScope.isEmpty then
        throw (.targetNotRepeatable target.checked.declaration.path)
      else
        let sourceBinding ← checkBoundCompleteDateTimeSource model declaringGroup
          target.checked.declaration.path
          target.checked.declaration.repeatableScope sourceReference
          |>.mapError .source
        pure {
          declaringGroup, target, sourceBinding
          declaringGroupValid := hValid
          targetContainedInDeclaringGroup := hGroup
          targetRepeatable := by
            intro empty
            simp [empty] at hRepeatable
        }
    else
      throw (.targetOutsideDeclaringGroup
        target.checked.declaration.path declaringGroup)
  else
    throw (.targetLookup (.invalidRuleGroup declaringGroup))

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

private def evaluateAtWithRead
    (operation : CheckedAddressedTimeFromDateTime model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
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
  let operand ← readTimeFromDateTimeSourceAtWithRead
    operation.sourceBinding.source sourceAddress .computation read
      |>.mapError .source
  let outcome := operation.target.evaluate operand.asTimeComputationResult
  pure { sourceField := sourceAddress, targetField := targetAddress, outcome }

/-- Execute once per physically instantiated target row while reading through one caller-supplied transient overlay. Target-row ownership remains with the immutable checked input. -/
def executeWithRead (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedTimeFromDateTimeFault
      (List AddressedTimeFromDateTimeOutcome) := do
  let environments ←
    input.computationRowEnvironments operation.target.checked.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead read)

/-- Execute once per physically instantiated target row in document order against the immutable input. -/
def execute (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedTimeFromDateTimeFault
      (List AddressedTimeFromDateTimeOutcome) :=
  operation.executeWithRead input input.read

/-- Execute through one caller-supplied transient read and classify every rich Time outcome against immutable source state at its exact target address. -/
def executeResultWithRead (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedTimeFromDateTimeFault
      (AddressedTimeFromDateTimeRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure (AddressedTimeFromDateTimeRunView.fromOutcomes operation input
    residualMessages outcomes)

/-- Execute every physical target row and classify each rich Time outcome against immutable source state at that exact target address. -/
def executeResult (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except AddressedTimeFromDateTimeFault
      (AddressedTimeFromDateTimeRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

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
