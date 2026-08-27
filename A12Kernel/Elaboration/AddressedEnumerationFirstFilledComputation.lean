import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.EnumerationFirstFilledComputation

/-! # Repeatable Enumeration `FirstFilledValue`

This capsule composes the established checked Enumeration first-filled source with one exact repeatable Enumeration target. Each physical target row supplies the outer environment for its own lazy source scan, and the resulting token, no-value, or poison stays attached to that row through the shared Enumeration result and cell-state application fold.

Scheduling and overlay construction, row reconstruction, and later validation remain separate. A caller may supply an already-constructed exact-address read view.
-/

namespace A12Kernel

inductive AddressedEnumerationFirstFilledComputationElabError where
  | target (cause : AddressedEnumerationComputationElabError)
  | source (cause : EnumerationFirstFilledComputationElabError)
  | sourceIncompatible (sourcePath targetPath : List String)
  | targetSelfReference (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One repeatable Enumeration target and complete checked first-filled source tied to the same validated model. -/
structure CheckedAddressedEnumerationFirstFilledComputation
    (model : FlatModel) where
  private mk ::
  target : CheckedAddressedEnumerationTarget model
  source : CheckedEnumerationFirstFilledSource model
    target.declaration.repeatableScope
  sourceAllowed : source.allowedFor target.projection = true
  targetNotReferenced : source.referencesField target.field = false

/-- Check the target before the shared first-filled source, then retain whole-domain compatibility and target exclusion as certificates. -/
def checkAddressedEnumerationFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationFirstFilledSource) :
    Except AddressedEnumerationFirstFilledComputationElabError
      (CheckedAddressedEnumerationFirstFilledComputation model) := do
  let target ← checkAddressedEnumerationTarget model declaringGroup targetField
    |>.mapError .target
  let source ← elaborateEnumerationFirstFilledSource model declaringGroup
      target.declaration.repeatableScope authored
    |>.mapError .source
  if hReference : source.referencesField target.field = true then
    throw (.targetSelfReference target.field)
  else if hAllowed : source.allowedFor target.projection = true then
    pure {
      target
      source
      sourceAllowed := hAllowed
      targetNotReferenced := by
        cases hValue : source.referencesField target.field with
        | false => rfl
        | true => exact False.elim (hReference hValue)
    }
  else
    match source.operands.find? fun operand =>
        !operand.allowedFor target.projection with
    | some operand =>
        throw (.sourceIncompatible operand.path target.declaration.path)
    | none => throw .incoherentCore

inductive AddressedEnumerationFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- One checked repeatable `FirstFilledValue` result backed by the common exact-address String channels. Retaining the producing operation prevents an unrelated target/action pair from inhabiting this route. -/
structure AddressedEnumerationFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedEnumerationFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedEnumerationFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedEnumerationFirstFilledComputationFault
      AddressedEnumerationComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.declaration.repeatableScope
      |>.mapError .targetEnvironment
  let selected ←
    operation.source.evaluateCheckedDocumentWithRead input read environment
    |>.mapError .source
  pure {
    targetField := { field := operation.target.field, path := targetPath }
    result := selected.asComputationResult
  }

/-- Execute one lazy first-filled scan per physical target row through a caller-supplied exact-address view. -/
def executeWithRead
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedEnumerationFirstFilledComputationFault
      (List AddressedEnumerationComputationOutcome) := do
  let environments ← input.actualRowEnvironments
      operation.target.declaration.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead input read)

/-- Execute one lazy first-filled scan per physical target row in document order. -/
def execute (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationFirstFilledComputationFault
      (List AddressedEnumerationComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Execute through one caller-supplied exact-address view and classify the resulting rows while retaining the checked Enumeration operation that produced them. -/
def executeResultWithRead
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedEnumerationFirstFilledComputationFault
      (AddressedEnumerationFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure {
    operation
    string := projectAddressedTokenResults input residualMessages outcomes
  }

/-- Classify exact row outcomes against the immutable source target state through the shared model-certified Enumeration result. -/
def executeResult
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedEnumerationFirstFilledComputationFault
      (AddressedEnumerationFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedEnumerationFirstFilledComputation

namespace AddressedEnumerationFirstFilledComputationRunView

/-- Apply only retained exact-address actions to a separate same-model destination cell-state projection. -/
def applyToChecked
    (view : AddressedEnumerationFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end AddressedEnumerationFirstFilledComputationRunView

end A12Kernel
