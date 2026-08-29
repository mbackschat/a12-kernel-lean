import A12Kernel.Elaboration.DateFromDateTime

/-! # Repeatable `DateFromDateTime`

This bounded carrier certifies one target-bound complete DateTime source and full-Date target, enumerates only physical target rows, and retains exact source and target addresses. Its result and cell-state application reuse the common FullDate channels; sibling parallel iteration, scheduling, row reconstruction, and document materialization remain separate.
-/

namespace A12Kernel

inductive AddressedDateFromDateTimeElabError where
  | targetLookup (cause : ResolveError)
  | target (cause : FullDateTargetElabError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | source (cause : BoundCompleteDateTimeSourceElabError)
  deriving Repr, DecidableEq

/-- One exact repeatable extraction certified against a validated model. -/
structure CheckedAddressedDateFromDateTime (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  target : CheckedFullDateTarget model
  sourceBinding : CheckedBoundCompleteDateTimeSource model declaringGroup
    target.checked.declaration.repeatableScope
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetContainedInDeclaringGroup :
    GroupPath.isPrefixOf declaringGroup target.checked.declaration.groupPath = true
  targetRepeatable : target.checked.declaration.repeatableScope ≠ []

/-- Certify one source whose repeatable levels the target's own scope binds. -/
def checkAddressedDateFromDateTime
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedDateFromDateTimeElabError
      (CheckedAddressedDateFromDateTime model) := do
  let targetDeclaration ← model.lookupUniqueId targetField |>.mapError .targetLookup
  let target ← elaborateFullDateTargetIn model
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
    throw (.targetOutsideDeclaringGroup target.checked.declaration.path declaringGroup)
  else
    throw (.targetLookup (.invalidRuleGroup declaringGroup))

inductive AddressedDateFromDateTimeFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  | sourceValueKind (source : CellAddr)
  | sourceExtractionUnavailable (source : CellAddr)
  | target (cause : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One row-local outcome with both addresses needed by Execute and Explain consumers. -/
structure AddressedDateFromDateTimeOutcome where
  sourceField : CellAddr
  targetField : CellAddr
  outcome : FullDateTargetOutcome
  deriving Repr, DecidableEq

/-- One checked addressed extraction result backed by the common FullDate channels over exact cell addresses. Retaining the checked operation ties every action to its admitted target declaration and row scope. -/
structure AddressedDateFromDateTimeRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedDateFromDateTime model
  fullDate : FullDateComputationRunView ResidualMessage CellAddr

namespace AddressedDateFromDateTimeRunView

/-- Classify executed row outcomes against immutable source state at each exact target address. -/
private def fromOutcomes (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedDateFromDateTimeOutcome) :
    AddressedDateFromDateTimeRunView model ResidualMessage := {
  operation
  fullDate := FullDateComputationRunView.fromOutcomesAt
    input.sourceFullDateTargetStateAt residualMessages
    (outcomes.map fun entry => (entry.targetField, entry.outcome))
}

end AddressedDateFromDateTimeRunView

namespace CheckedAddressedDateFromDateTime

/-- Classify one reached source cell without losing clean absence or formal poison. -/
def evaluateSourceCell (operation : CheckedAddressedDateFromDateTime model)
    (sourceAddress : CellAddr) (cell : CheckedCell) :
    Except AddressedDateFromDateTimeFault TemporalComputationResult :=
  match observeCell .computation cell with
  | .empty => pure .noValue
  | .poison cause | .unknown cause => pure (.poison cause)
  | .value (.temporal value) =>
      match dateFromDateTime? operation.target.profile value with
      | some date => pure (.value date.instant)
      | none => throw (.sourceExtractionUnavailable sourceAddress)
  | .value _ => throw (.sourceValueKind sourceAddress)

private def evaluateAtWithRead
    (operation : CheckedAddressedDateFromDateTime model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedDateFromDateTimeFault AddressedDateFromDateTimeOutcome := do
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
  let sourceCell ← read sourceAddress |>.mapError .sourceRead
  let result ← operation.evaluateSourceCell sourceAddress sourceCell
  let outcome ← operation.target.evaluate result |>.mapError .target
  pure { sourceField := sourceAddress, targetField := targetAddress, outcome }

/-- Execute once per physically instantiated target row while reading through one caller-supplied transient overlay. Target-row ownership remains with the immutable checked input. -/
def executeWithRead (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedDateFromDateTimeFault
      (List AddressedDateFromDateTimeOutcome) := do
  let environments ←
    input.actualRowEnvironments operation.target.checked.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead read)

/-- Execute once per physically instantiated target row in document order against the immutable input. -/
def execute (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedDateFromDateTimeFault
      (List AddressedDateFromDateTimeOutcome) :=
  operation.executeWithRead input input.read

/-- Execute through one caller-supplied transient read and classify each rich FullDate outcome against immutable source target state. -/
def executeResultWithRead (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedDateFromDateTimeFault
      (AddressedDateFromDateTimeRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure (AddressedDateFromDateTimeRunView.fromOutcomes operation input
    residualMessages outcomes)

/-- Execute every physical target row against the immutable input and classify each rich FullDate outcome at its exact target address. -/
def executeResult (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except AddressedDateFromDateTimeFault
      (AddressedDateFromDateTimeRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedDateFromDateTime

namespace AddressedDateFromDateTimeRunView

/-- Apply retained source-relative actions to exact FullDate cell-state projections from a separately supplied checked document of the same model. The result does not reconstruct rows or a document. -/
def applyToChecked
    (view : AddressedDateFromDateTimeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (FullDateComputationRunView.FullDateComputationRunApplicationError
      CellAddr) (FullDateComputationDestination CellAddr) :=
  view.fullDate.applyTo destination.sourceFullDateTargetStateAt

end AddressedDateFromDateTimeRunView

end A12Kernel
