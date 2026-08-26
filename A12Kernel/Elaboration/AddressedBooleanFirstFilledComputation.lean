import A12Kernel.Elaboration.BooleanFirstFilledComputation

/-! # Exact-address repeatable Boolean `FirstFilledValue`

This capsule binds one repeatable Boolean target to a one-axis starred Boolean source. Repeatable levels above the star are supplied by each physical target environment, so a sibling source extent stays correlated to its enclosing row. Result classification and application reuse the typed Boolean channels without reconstructing a document or running validation.
-/

namespace A12Kernel

inductive AddressedBooleanFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetKind (path : List String) (actual : SurfaceScalarKind)
  | source (cause : StarPathElabError)
  | sourceKind (path : List String) (actual : SurfaceScalarKind)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable Boolean target and one checked single-reopened-axis Boolean source tied to the same validated model. -/
structure CheckedAddressedBooleanFirstFilledComputation (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  targetField : FieldId
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  targetOwned : model.lookupUniqueId targetField = .ok target
  targetInDeclaringGroup : target.groupPath = declaringGroup
  targetBoolean : target.policy.kind = .boolean
  targetRepeatable : target.repeatableScope ≠ []
  sourceBoolean : source.declaration.policy.kind = .boolean
  sourceSingleReopenedAxis : source.reopenedScope.length = 1
  sourceBindingBound :
    source.bindingScope.all target.repeatableScope.contains = true
  targetNotReferenced : source.declaration.id ≠ targetField

/-- Check the target first, then certify one Boolean star whose outer binding scope is available at every target row. -/
def checkAddressedBooleanFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedBooleanFirstFilledComputationElabError
      (CheckedAddressedBooleanFirstFilledComputation model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error cause => .error (.target cause)
  | .ok target => do
    if hGroup : target.groupPath = declaringGroup then
      if hRepeatable : target.repeatableScope.isEmpty then
        throw (.targetNotRepeatable target.path)
      else if hTargetKind : target.policy.kind = .boolean then
        let source ← elaborateStarFieldPath model declaringGroup authored
          |>.mapError .source
        if hSourceKind : source.declaration.policy.kind = .boolean then
          if hShape : source.reopenedScope.length = 1 then
            if hScope :
                source.bindingScope.all target.repeatableScope.contains = true then
              if hSelf : source.declaration.id = targetField then
                throw (.targetSelfReference targetField)
              else
                pure {
                  declaringGroup
                  targetField
                  target
                  source
                  targetOwned := hTarget
                  targetInDeclaringGroup := hGroup
                  targetBoolean := hTargetKind
                  targetRepeatable := by
                    intro empty
                    simp [empty] at hRepeatable
                  sourceBoolean := hSourceKind
                  sourceSingleReopenedAxis := hShape
                  sourceBindingBound := hScope
                  targetNotReferenced := hSelf
                }
            else
              throw (.sourceScope source.declaration.path)
          else
            throw (.sourceShape source.declaration.path)
        else
          throw (.sourceKind source.declaration.path
            source.declaration.policy.kind.surfaceKind)
      else
        throw (.targetKind target.path target.policy.kind.surfaceKind)
    else
      throw (.targetOutsideDeclaringGroup target.path declaringGroup)

inductive AddressedBooleanFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- One row-local Boolean selection retained under its exact target address. -/
structure AddressedBooleanFirstFilledComputationOutcome where
  targetField : CellAddr
  result : FirstFilledBooleanComputationResult
  deriving Repr, DecidableEq

/-- One checked addressed Boolean result backed by the shared typed Boolean channels. -/
structure AddressedBooleanFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedBooleanFirstFilledComputation model
  boolean : BooleanComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedBooleanFirstFilledComputation

private def evaluateAt
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedBooleanFirstFilledComputationFault
      AddressedBooleanFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedField input environment
    |>.mapError .source
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    result := evalFirstFilledBoolean
      (resolved.cells.map fun cell => booleanFirstFilledCellAt cell.cell)
  }

/-- Execute one sibling-correlated first-filled scan per physical target row in document order. -/
def execute
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedBooleanFirstFilledComputationFault
      (List AddressedBooleanFirstFilledComputationOutcome) := do
  let environments ← input.actualRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAt input)

/-- Classify every exact row outcome against immutable source target state through the shared Boolean result owner. -/
def executeResult
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedBooleanFirstFilledComputationFault
      (AddressedBooleanFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure {
    operation
    boolean := BooleanComputationRunView.fromSourcedOutcomes residualMessages
      (outcomes.map fun entry =>
        (entry.targetField, entry.result,
          input.sourceBooleanTargetStateAt entry.targetField))
  }

end CheckedAddressedBooleanFirstFilledComputation

namespace AddressedBooleanFirstFilledComputationRunView

/-- Apply only retained exact-address Boolean actions to a separate same-model destination projection. -/
def applyToChecked
    (view : AddressedBooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    BooleanComputationDestination CellAddr :=
  view.boolean.applyTo destination.sourceBooleanTargetStateAt

end AddressedBooleanFirstFilledComputationRunView

end A12Kernel
