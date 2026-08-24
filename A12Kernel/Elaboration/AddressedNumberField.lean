import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Repeatable direct Number-field computation -/

namespace A12Kernel

/-- Fail-closed errors for one addressed direct Number source before any operation-specific result-scale check. -/
inductive AddressedNumberSourceElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | sourceNotNumber (path : List String) (actual : SurfaceScalarKind)
  deriving Repr, DecidableEq

/-- One direct Number source certified on the shared repeatable placement. -/
structure CheckedAddressedNumberSource (model : FlatModel) where
  private mk ::
  placement : CheckedAddressedNumericPlacement model
  source : FlatNumberField
  sourceCertified :
    placement.sourceDeclaration.toNumberField? = some source

/-- Validate the direct Number source once, before a computation wrapper applies its own result-scale contract. -/
def checkAddressedNumberSource
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedNumberSourceElabError
      (CheckedAddressedNumberSource model) :=
  match checkAddressedNumericPlacement model declaringGroup
      targetField sourceReference with
  | .error cause => .error (.placement cause)
  | .ok placement =>
    match hSource : placement.sourceDeclaration.toNumberField? with
    | none =>
        .error (.sourceNotNumber placement.sourceDeclaration.path
          placement.sourceDeclaration.policy.kind.surfaceKind)
    | some source => .ok { placement, source, sourceCertified := hSource }

/-- Fail-closed errors shared by operations over two ordered direct Number sources. -/
inductive AddressedNumberPairElabError where
  | left (cause : AddressedNumberSourceElabError)
  | right (cause : AddressedNumberSourceElabError)
  | incoherentTarget (left right : FieldId)
  deriving Repr, DecidableEq

/-- Two ordered direct Number sources certified against one exact target placement. -/
structure CheckedAddressedNumberPair (model : FlatModel) where
  private mk ::
  left : CheckedAddressedNumberSource model
  right : CheckedAddressedNumberSource model
  sameTarget : left.placement.targetField = right.placement.targetField

/-- Validate two ordered direct Number sources once, before an operation-specific result-scale check. -/
def checkAddressedNumberPair
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath) :
    Except AddressedNumberPairElabError
      (CheckedAddressedNumberPair model) := do
  let left ←
    checkAddressedNumberSource model declaringGroup targetField leftReference
      |>.mapError .left
  let right ←
    checkAddressedNumberSource model declaringGroup targetField rightReference
      |>.mapError .right
  if hTarget : left.placement.targetField = right.placement.targetField then
    pure { left, right, sameTarget := hTarget }
  else
    throw (.incoherentTarget left.placement.targetField
      right.placement.targetField)

/-- Fail-closed errors specific to direct addressed Number assignment. -/
inductive AddressedNumberFieldElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | sourceNotNumber (path : List String) (actual : SurfaceScalarKind)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One direct Number assignment whose shared source certificate also matches the target scale exactly. -/
structure CheckedAddressedNumberField (model : FlatModel)
    extends CheckedAddressedNumberSource model where
  sameScale :
    placement.targetPolicy.info.scale = source.info.scale

/-- Validate the direct Number source and exact assignment scale on the shared addressed placement. -/
def checkAddressedNumberField
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedNumberFieldElabError
      (CheckedAddressedNumberField model) :=
  match checkAddressedNumberSource model declaringGroup
      targetField sourceReference with
  | .error (.placement cause) => .error (.placement cause)
  | .error (.sourceNotNumber path actual) =>
      .error (.sourceNotNumber path actual)
  | .ok numberSource =>
    if hScale : numberSource.placement.targetPolicy.info.scale =
        numberSource.source.info.scale then
      .ok {
        toCheckedAddressedNumberSource := numberSource
        sameScale := hScale
      }
    else
      .error (.scaleMismatch numberSource.placement.targetPolicy.info.scale
        numberSource.source.info.scale)

abbrev AddressedNumberFieldFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberSource

/-- Read and evaluate this direct Number source at the row environment through a caller-supplied
exact-address view. The source addresses at its **own** repeatable scope, which the placement
certifies the target's scope binds, so an outer-scope operand resolves to its own shorter path
rather than borrowing the target's. -/
def evaluateAtEnvironmentWithRead
    (source : CheckedAddressedNumberSource model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult := do
  let path ←
    (environment.pathForScope
      source.placement.sourceDeclaration.repeatableScope).mapError .environment
  let address : CellAddr := {
    field := source.placement.sourceDeclaration.id
    path
  }
  let cell ← (read address).mapError .sourceRead
  (source.placement.evaluateSourceAtom cell
    (.field source.placement.sourceDeclaration)).mapError .evaluation

/-- Read and evaluate this direct Number source against the immutable checked document. -/
def evaluateAtEnvironment
    (source : CheckedAddressedNumberSource model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult :=
  source.evaluateAtEnvironmentWithRead input.read environment

end CheckedAddressedNumberSource

namespace CheckedAddressedNumberPair

/-- Evaluate both sources through a caller-supplied exact-address view in authored order, each at its own repeatable scope. A left poison prevents the right source from being reached; the caller supplies the scalar operation over reached outcomes. -/
def evaluateAtEnvironmentWithRead
    (pair : CheckedAddressedNumberPair model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (environment : Env) :
  Except AddressedNumericLeafFault NumericComputationResult := do
  let leftResult ← pair.left.evaluateAtEnvironmentWithRead read environment
  match leftResult with
  | .poison cause => pure (.poison cause)
  | .value _ | .domainFailure =>
      let rightResult ← pair.right.evaluateAtEnvironmentWithRead read environment
      pure (combine leftResult rightResult)

/-- Evaluate both sources against the immutable checked document. -/
def evaluateAtEnvironment
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult :=
  pair.evaluateAtEnvironmentWithRead input.read combine environment

/-- Execute two direct Number sources through a caller-supplied exact-address view and the ordinary target checker. -/
def executeWithRead
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  pair.left.placement.executeAtEnvironment input
    (pair.evaluateAtEnvironmentWithRead read combine)

/-- Execute two direct Number sources in authored order at the same row environment through the ordinary target checker. A left poison prevents the right source from being reached. -/
def executeWith
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  pair.executeWithRead input input.read combine

/-- Execute two direct Number sources through the same target's warning-suppressed checker. -/
def executeWithScaleWarningSuppressed
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  pair.left.placement.executeAtEnvironmentScaleWarningSuppressed input
    (pair.evaluateAtEnvironment input combine)

private def resultFromOutcomes
    (outcomes : List (SourcedNumericTargetOutcome CellAddr))
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    NumericComputationRunView
      (ComputationFormalMessage Payload) CellAddr :=
  NumericComputationRunView.fromSourceOutcomesWithMessages
    MessagePointer.ofCellAddr payloadAt supplied outcomes

/-- Classify a two-source addressed execution through the ordinary unsuppressed target checker. -/
def executeResultWith
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumericLeafFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  (pair.executeWith input combine).map fun outcomes =>
    resultFromOutcomes outcomes payloadAt supplied

/-- Classify a warning-suppressed two-source execution against the immutable source document. -/
def executeResultWithScaleWarningSuppressed
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumericLeafFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  (pair.executeWithScaleWarningSuppressed input combine).map fun outcomes =>
    resultFromOutcomes outcomes payloadAt supplied

end CheckedAddressedNumberPair

namespace CheckedAddressedNumberField

private def evaluateSource
    (operation : CheckedAddressedNumberField model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  operation.placement.evaluateSourceAtom sourceCell
    (.field operation.placement.sourceDeclaration)

/-- Execute the direct Number read through a caller-supplied exact-address view while target iteration and prior-target classification remain owned by the immutable checked document. -/
def executeWithRead (operation : CheckedAddressedNumberField model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedNumberFieldFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.placement.executeWithRead input read operation.evaluateSource

/-- Execute the certified direct Number read through the shared addressed placement. -/
def execute (operation : CheckedAddressedNumberField model)
    (input : CheckedDocument model) :
    Except AddressedNumberFieldFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.executeWithRead input input.read

/-- Classify exact addressed outcomes against the immutable source document. -/
def executeResult
    (operation : CheckedAddressedNumberField model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberFieldFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedNumberField

end A12Kernel
