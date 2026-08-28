import A12Kernel.Elaboration.AddressedFirstFilledStar
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Elaboration.StringFirstFilledComputation

/-! # Exact-address repeatable ordinary String `FirstFilledValue`

This capsule binds one repeatable ordinary String target to one sibling single-axis ordinary String star. Every physical target row supplies the nonempty proper outer binding prefix. Selection reuses the fixed String first-filled scan, then the exact declaration-owned target policy and prepared matcher classify the selected root store at its exact address.
-/

namespace A12Kernel

inductive AddressedStringFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetNotOrdinaryString (path : List String)
  | source (cause : StarPathElabError)
  | sourceNotOrdinaryString (path : List String)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable ordinary String target and one checked sibling star carrying ordinary evaluated Strings. -/
structure CheckedAddressedStringFirstFilledComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  checkedSource : CheckedStarFieldPath model
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource
  targetOrdinary :
    checkedTarget.declaration.isOrdinaryStringComputationCarrier = true
  sourceOrdinary :
    checkedSource.declaration.isOrdinaryStringComputationCarrier = true
  sourceBindingPrefix : checkedSource.bindingScope.isPrefixOf
    checkedTarget.declaration.repeatableScope = true
  sourceBindingStrict :
    checkedSource.bindingScope ≠ checkedTarget.declaration.repeatableScope

namespace CheckedAddressedStringFirstFilledComputation

def targetField
    (operation : CheckedAddressedStringFirstFilledComputation model) : FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedStringFirstFilledComputation model) :
    FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedStringFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

end CheckedAddressedStringFirstFilledComputation

private def mapAddressedStringTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedStringFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedStringPlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedStringFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check repeatable target placement, ordinary String carrier identity, and the sibling-star binding certificate. -/
def checkAddressedStringFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedStringFirstFilledComputationElabError
      (CheckedAddressedStringFirstFilledComputation model) := do
  let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
    |>.mapError mapAddressedStringTargetError
  if hTarget :
      target.declaration.isOrdinaryStringComputationCarrier = true then
    let source ← elaborateStarFieldPath model declaringGroup authored
      |>.mapError .source
    if hSource :
        source.declaration.isOrdinaryStringComputationCarrier = true then
      if hPrefix :
          source.bindingScope.isPrefixOf target.declaration.repeatableScope then
        if hStrict :
            source.bindingScope = target.declaration.repeatableScope then
          throw (.sourceScope source.declaration.path)
        else
          let placement ← checkAddressedFirstFilledStarPlacement target source
            |>.mapError mapAddressedStringPlacementError
          pure {
            checkedTarget := target
            checkedSource := source
            placement
            targetOrdinary := hTarget
            sourceOrdinary := hSource
            sourceBindingPrefix := hPrefix
            sourceBindingStrict := hStrict
          }
      else
        throw (.sourceScope source.declaration.path)
    else
      throw (.sourceNotOrdinaryString source.declaration.path)
  else
    throw (.targetNotOrdinaryString target.declaration.path)

inductive AddressedStringFirstFilledComputationFault where
  | targetPatternUnavailable (field : FieldId)
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- One exact-address ordinary String target outcome before source-relative result classification. -/
structure AddressedStringFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : StringTargetOutcome
  deriving Repr, DecidableEq

/-- One addressed ordinary String result retaining its exact checked operation. -/
structure AddressedStringFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedStringFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedStringFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (matcher : Option (String → Bool)) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedStringFirstFilledComputationFault
      AddressedStringFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedFieldWithRead input read environment
    |>.mapError .source
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    outcome := operation.target.stringPolicy.checkTargetWithPattern matcher
      (CheckedStringFirstFilledComputation.evalResolvedStringFirstFilled
        resolved).asStringStore
  }

/-- Execute one parent-local ordinary String scan through a caller-supplied exact-address source view, then apply the one prepared target matcher. Target topology, pattern preparation, and immutable target state remain unchanged. -/
def executeWithRead
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedStringFirstFilledComputationFault
      (List AddressedStringFirstFilledComputationOutcome) := do
  let matcher ← match patterns.targetMatcher? operation.targetField with
    | some matcher => pure matcher
    | none => throw (.targetPatternUnavailable operation.targetField)
  let environments ← input.actualRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead matcher input read)

/-- Execute one parent-local ordinary String scan per physical target row, then apply the one prepared target matcher. -/
def execute
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except AddressedStringFirstFilledComputationFault
      (List AddressedStringFirstFilledComputationOutcome) :=
  operation.executeWithRead patterns input input.read

/-- Classify caller-view outcomes against the immutable source target at that same address. -/
def executeResultWithRead
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedStringFirstFilledComputationFault
      (AddressedStringFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead patterns input read
  pure {
    operation
    string := StringComputationRunView.fromSourcedOutcomes residualMessages
      (outcomes.map fun entry => {
        targetField := entry.targetField
        outcome := entry.outcome
        source := input.sourceStringTargetStateAt entry.targetField
      })
  }

/-- Classify every exact rich outcome against the immutable source target at that same address. -/
def executeResult
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedStringFirstFilledComputationFault
      (AddressedStringFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead patterns input input.read residualMessages

end CheckedAddressedStringFirstFilledComputation

namespace AddressedStringFirstFilledComputationRunView

/-- Apply retained exact-address actions to a separate same-model destination projection without reclassifying them. -/
def applyToChecked
    (view : AddressedStringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError
      CellAddr) (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end AddressedStringFirstFilledComputationRunView

end A12Kernel
