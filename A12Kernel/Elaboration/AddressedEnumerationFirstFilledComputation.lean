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

namespace AddressedEnumerationFirstFilledComputationElabError

def calculationRefusal? : AddressedEnumerationFirstFilledComputationElabError → Option CalculationRefusal
  | .source cause => cause.calculationRefusal?
  | .sourceIncompatible _ _ => some .invalidEnumCalculation
  | _ => none

end AddressedEnumerationFirstFilledComputationElabError

/-- One repeatable Enumeration target and complete checked first-filled source tied to the same validated model. -/
structure CheckedAddressedEnumerationFirstFilledComputation
    (model : FlatModel) where
  private mk ::
  target : CheckedAddressedEnumerationTarget model
  source : CheckedEnumerationFirstFilledSource model
    target.declaration.repeatableScope
  sourceAllowed : source.allowedFor target.projection = true
  targetNotReferenced : source.referencesWith target.field (·.forbidsTarget target.field) = false

/-- Check the target before the shared first-filled source, then retain whole-domain compatibility and target exclusion as certificates. -/
def checkAddressedEnumerationFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceEnumerationFirstFilledSource) :
    Except AddressedEnumerationFirstFilledComputationElabError
      (CheckedAddressedEnumerationFirstFilledComputation model) := do
  let target ← checkAddressedEnumerationTarget model declaringGroup targetField
    |>.mapError .target
  -- The declaring group, not the target, places a refusal here; no row measures this carrier's
  -- placement ([SG9](../../docs/gaps/paths-and-groups.md)).
  let source ← elaborateEnumerationFirstFilledSource model declaringGroup
      target.declaration.repeatableScope authored declaringGroup target.declaration.groupPath
    |>.mapError .source
  if hReference : source.referencesWith target.field (·.forbidsTarget target.field) = true then
    throw (.targetSelfReference target.field)
  else if hAllowed : source.allowedFor target.projection = true then
    pure {
      target
      source
      sourceAllowed := hAllowed
      targetNotReferenced := by
        cases hValue : source.referencesWith target.field (·.forbidsTarget target.field) with
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

/-- Evaluate one target instance through the caller's read view, preserving filter failures for its handler. -/
def evaluateAtWithRead
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env)
    (world : Option World := none) :
    Except AddressedEnumerationFirstFilledComputationFault
      AddressedEnumerationComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.declaration.repeatableScope
      |>.mapError .targetEnvironment
  let selected ←
    operation.source.evaluateCheckedDocumentWithRead (world := world) input read environment
    |>.mapError .source
  pure {
    targetField := { field := operation.target.field, path := targetPath }
    result := selected.asComputationResult
  }

/-- The no-value outcome an over-limit target row takes instead of a computation, retaining its
exact address so the application projection clears it. -/
def clearedAt (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (environment : Env) :
    Except AddressedEnumerationFirstFilledComputationFault
      AddressedEnumerationComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.declaration.repeatableScope
      |>.mapError .targetEnvironment
  pure {
    targetField := { field := operation.target.field, path := targetPath }
    result := .noValue
  }

/-- Execute one lazy first-filled scan per **in-capacity** target row through a caller-supplied exact-address view, and only a clear at each over-limit row. -/
def executeWithRead
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    Except AddressedEnumerationFirstFilledComputationFault
      (List AddressedEnumerationComputationOutcome) := do
  input.computationRowOutcomes operation.target.declaration.repeatableScope .targetRows
    operation.clearedAt (operation.evaluateAtWithRead (world := world) input read)

/-- Execute one lazy first-filled scan per in-capacity target row in document order, and a clear at each over-limit row. -/
def execute (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (world : Option World := none) :
    Except AddressedEnumerationFirstFilledComputationFault
      (List AddressedEnumerationComputationOutcome) :=
  operation.executeWithRead (world := world) input input.read

/-- Execute through one caller-supplied exact-address view and classify the resulting rows while retaining the checked Enumeration operation that produced them. -/
def executeResultWithRead
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage)
    (world : Option World := none) :
    Except AddressedEnumerationFirstFilledComputationFault
      (AddressedEnumerationFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead (world := world) input read
  pure {
    operation
    string := projectAddressedTokenResults input residualMessages outcomes
  }

/-- Classify exact row outcomes against the immutable source target state through the shared model-certified Enumeration result. -/
def executeResult
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (world : Option World := none) :
    Except AddressedEnumerationFirstFilledComputationFault
      (AddressedEnumerationFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead (world := world) input input.read residualMessages

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
